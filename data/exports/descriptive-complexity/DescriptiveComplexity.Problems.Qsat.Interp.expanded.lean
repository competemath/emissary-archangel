/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Qsat.Tags
import DescriptiveComplexity.Problems.Qsat.Defs
import DescriptiveComplexity.Padding


-- @@ L11-36 verbatim
/-!
# The interpretation of the Savitch reduction

The defining formulas of the reduction of SUCCINCT-REACH to QSAT, and the
resulting first-order interpretation `DescriptiveComplexity.qsatInterp`, of
dimension `2` over the ordered expansion of `FirstOrder.Language.transSys`.

Every relation of `FirstOrder.Language.qsat` is defined by a formula that only
depends on the *tags* of its arguments, and each of those formulas is read off
the tables of `DescriptiveComplexity.Problems.Qsat.Tags`:

* `DescriptiveComplexity.QsatRed.varF` and `DescriptiveComplexity.QsatRed.clF` are the marks
  `DescriptiveComplexity.QVarOn` and `DescriptiveComplexity.QClOn`;
* `DescriptiveComplexity.QsatRed.occF` collects, from the fixed literal list
  `DescriptiveComplexity.qLits` of a clause tag, those literals that are on the
  variable tag and sign asked for – so a single generic realization lemma
  (`DescriptiveComplexity.QsatRed.realize_occF`) replaces a case analysis on all pairs of
  tags;
* `DescriptiveComplexity.QsatRed.prefF` is the lexicographic comparison
  `DescriptiveComplexity.KeyLt` of the two keys, built from static numerals and
  two order atoms.

The section “Characterization of the interpreted relations” reads each of them
back through `DescriptiveComplexity.FOInterpretation.relMap_map`; those lemmas are
the only interface the correctness proof uses.
-/


-- @@ L38-38 verbatim
namespace DescriptiveComplexity


-- @@ L40-40 verbatim
open FirstOrder


-- @@ L42-42 verbatim
open Language Structure


-- @@ L44-48 verbatim
/-! ### The formula builders of the reduction

They live in their own namespace: short names like `leF` or `occF` are what every
reduction of the library calls its builders, and the umbrella
`DescriptiveComplexity.Problems` imports them all at once. -/


-- @@ L50-50 verbatim
namespace QsatRed


-- @@ L52-54 verbatim
/-- The ordered expansion of the vocabulary of transition systems: the source
vocabulary of the reduction. -/
abbrev transOrd : Language := Language.transSys.sum Language.order


-- @@ L56-57 verbatim
/-- The symbol for “is a state variable”, in the ordered expansion. -/
abbrev svSym : transOrd.Relations 1 := Sum.inl tsStateVar


-- @@ L59-60 verbatim
/-- The symbol for “is a source clause”, in the ordered expansion. -/
abbrev srcSym : transOrd.Relations 1 := Sum.inl tsSrcCl


-- @@ L62-63 verbatim
/-- The symbol for “is a target clause”, in the ordered expansion. -/
abbrev tgtSym : transOrd.Relations 1 := Sum.inl tsTgtCl


-- @@ L65-66 verbatim
/-- The symbol for “is a transition clause”, in the ordered expansion. -/
abbrev stepSym : transOrd.Relations 1 := Sum.inl tsStepCl


-- @@ L68-69 verbatim
/-- The symbol for “is the next-state copy of”, in the ordered expansion. -/
abbrev nxtSym : transOrd.Relations 2 := Sum.inl tsNext


-- @@ L71-72 verbatim
/-- The symbol for “occurs positively in”, in the ordered expansion. -/
abbrev pSym : transOrd.Relations 2 := Sum.inl tsPosIn


-- @@ L74-75 verbatim
/-- The symbol for “occurs negatively in”, in the ordered expansion. -/
abbrev nSym : transOrd.Relations 2 := Sum.inl tsNegIn


-- @@ L77-77 verbatim
/-! ### Atomic formula builders -/


-- @@ L79-79 verbatim
section Atoms


-- @@ L81-81 verbatim
variable {α : Type}


-- @@ L83-84 verbatim
/-- `x` is a state variable, as a formula. -/
def svF (x : α) : transOrd.Formula α := Relations.formula₁ svSym (Term.var x)


-- @@ L86-87 verbatim
/-- `c` is a source clause, as a formula. -/
def srcF (c : α) : transOrd.Formula α := Relations.formula₁ srcSym (Term.var c)


-- @@ L89-90 verbatim
/-- `c` is a target clause, as a formula. -/
def tgtF (c : α) : transOrd.Formula α := Relations.formula₁ tgtSym (Term.var c)


-- @@ L92-93 verbatim
/-- `c` is a transition clause, as a formula. -/
def stepF (c : α) : transOrd.Formula α := Relations.formula₁ stepSym (Term.var c)


-- @@ L95-97 verbatim
/-- `y` is the next-state copy of `x`, as a formula. -/
def nxtF (x y : α) : transOrd.Formula α :=
  Relations.formula₂ nxtSym (Term.var x) (Term.var y)


-- @@ L99-101 verbatim
/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : transOrd.Formula α :=
  Relations.formula₂ pSym (Term.var c) (Term.var x)


-- @@ L103-105 verbatim
/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : transOrd.Formula α :=
  Relations.formula₂ nSym (Term.var c) (Term.var x)


-- @@ L107-109 verbatim
/-- `x ≤ y`, as a formula. -/
def leF (x y : α) : transOrd.Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)


-- @@ L111-112 verbatim
/-- `x = y`, as a formula. -/
def eqF (x y : α) : transOrd.Formula α := Term.equal (Term.var x) (Term.var y)


-- @@ L114-115 verbatim
/-- `x < y`, as a formula. -/
def ltF (x y : α) : transOrd.Formula α := leF x y ⊓ ∼(eqF x y)


-- @@ L117-118 verbatim
/-- `x` is a minimum of the input order, as a formula. -/
noncomputable def isBotF (x : α) : transOrd.Formula α := botF (L := Language.transSys) x


-- @@ L120-122 expanded
/-- `x` is the first state variable, as a formula. -/
noncomputable def minSVF (x : α) : transOrd.Formula α :=
  svF x ⊓
    FirstOrder.Language.BoundedFormula.not
      (FirstOrder.Language.Formula.iExs (Fin 1) (svF (Sum.inr 0) ⊓ ltF (Sum.inr 0) (Sum.inl x)))


-- @@ L124-126 expanded
/-- `x` is the last state variable, as a formula. -/
noncomputable def maxSVF (x : α) : transOrd.Formula α :=
  svF x ⊓
    FirstOrder.Language.BoundedFormula.not
      (FirstOrder.Language.Formula.iExs (Fin 1) (svF (Sum.inr 0) ⊓ ltF (Sum.inl x) (Sum.inr 0)))


-- @@ L128-131 expanded
/-- `x` is the state variable just above the state variable `y`, as a
formula. -/
noncomputable def predSVF (x y : α) : transOrd.Formula α :=
  svF x ⊓ svF y ⊓ ltF x y ⊓
    FirstOrder.Language.BoundedFormula.not
      (FirstOrder.Language.Formula.iExs (Fin 1)
        (svF (Sum.inr 0) ⊓ ltF (Sum.inl x) (Sum.inr 0) ⊓ ltF (Sum.inr 0) (Sum.inl y)))


-- @@ L133-133 verbatim
end Atoms


-- @@ L135-135 verbatim
/-! ### Realization of the atomic builders -/


-- @@ L137-137 verbatim
section RealizeAtoms


-- @@ L139-139 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] {α : Type} {V : α → A}


-- @@ L141-144 verbatim
@[simp]
theorem realize_svF {x : α} : (svF x).Realize V ↔ IsSV (V x) := by
  rw [svF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L146-149 verbatim
@[simp]
theorem realize_srcF {c : α} : (srcF c).Realize V ↔ RelMap tsSrcCl ![V c] := by
  rw [srcF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L151-154 verbatim
@[simp]
theorem realize_tgtF {c : α} : (tgtF c).Realize V ↔ RelMap tsTgtCl ![V c] := by
  rw [tgtF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L156-159 verbatim
@[simp]
theorem realize_stepF {c : α} : (stepF c).Realize V ↔ RelMap tsStepCl ![V c] := by
  rw [stepF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L161-164 verbatim
@[simp]
theorem realize_nxtF {x y : α} : (nxtF x y).Realize V ↔ RelMap tsNext ![V x, V y] := by
  rw [nxtF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L166-169 verbatim
@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize V ↔ RelMap tsPosIn ![V c, V x] := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L171-174 verbatim
@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize V ↔ RelMap tsNegIn ![V c, V x] := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L176-178 verbatim
@[simp]
theorem realize_leF {x y : α} : (leF x y).Realize V ↔ V x ≤ V y := by
  simp [leF, Formula.realize_rel₂]


-- @@ L180-182 verbatim
@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize V ↔ V x = V y := by
  simp [eqF]


-- @@ L184-186 verbatim
@[simp]
theorem realize_ltF {x y : α} : (ltF x y).Realize V ↔ V x < V y := by
  simp [ltF, lt_iff_le_and_ne]


-- @@ L188-190 verbatim
@[simp]
theorem realize_isBotF {x : α} : (isBotF x).Realize V ↔ IsBot (V x) :=
  realize_botF


-- @@ L192-200 verbatim
@[simp]
theorem realize_minSVF {x : α} : (minSVF x).Realize V ↔ IsMinSV (V x) := by
  simp only [minSVF, IsMinSV, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_svF, realize_ltF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun z hz hlt => h2 ⟨fun _ => z, hz, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hh => hh.elim fun i hi => h2 (i 0) hi.1 hi.2⟩


-- @@ L202-210 verbatim
@[simp]
theorem realize_maxSVF {x : α} : (maxSVF x).Realize V ↔ IsMaxSV (V x) := by
  simp only [maxSVF, IsMaxSV, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_svF, realize_ltF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun z hz hlt => h2 ⟨fun _ => z, hz, hlt⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hh => hh.elim fun i hi => h2 (i 0) hi.1 hi.2⟩


-- @@ L212-220 verbatim
@[simp]
theorem realize_predSVF {x y : α} : (predSVF x y).Realize V ↔ IsPredSV (V x) (V y) := by
  simp only [predSVF, IsPredSV, Formula.realize_inf, Formula.realize_not, Formula.realize_iExs,
    realize_svF, realize_ltF, Sum.elim_inl, Sum.elim_inr, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun z hz hlt => h4 ⟨fun _ => z, hz, hlt⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, fun hh => hh.elim fun i hi => h4 (i 0) hi.1 hi.2⟩


-- @@ L222-222 verbatim
end RealizeAtoms


-- @@ L224-224 verbatim
/-! ### The defining formulas -/


-- @@ L226-226 verbatim
section Formulas


-- @@ L228-228 verbatim
variable {α : Type}


-- @@ L230-235 verbatim
/-- The mark of a variable tag, as a formula in its two coordinates. -/
noncomputable def varF : QVarTag → α → α → transOrd.Formula α
  | .sS | .sT | .sB => fun p q => svF p ⊓ isBotF q
  | .sZ | .sU | .sV => fun p q => svF p ⊓ svF q
  | .aS | .aT | .aP => fun _ q => isBotF q
  | .sE => fun p q => isBotF p ⊓ isBotF q


-- @@ L237-246 verbatim
/-- The guard of a clause tag, as a formula in its two coordinates. -/
noncomputable def clF : QClTag → α → α → transOrd.Formula α
  | .cSrc => fun p q => srcF p ⊓ isBotF q
  | .cTgt => fun p q => tgtF p ⊓ isBotF q
  | .cStep => fun p q => stepF p ⊓ isBotF q
  | .lS _ | .lT _ => fun p q => svF p ⊓ isBotF q
  | .lU _ => fun p q => svF p ⊓ isBotF q
  | .lV _ => fun p q => svF p ⊓ nxtF p q
  | .bE _ => fun p q => svF p ⊓ isBotF q
  | .lev _ _ _ => fun p q => svF p ⊓ svF q


-- @@ L248-250 verbatim
/-- The mark of the universally quantified variables: only the bits `b_ℓ`. -/
noncomputable def allF (v : QVarTag) (p q : α) : transOrd.Formula α :=
  if v = .sB then varF v p q else ⊥


-- @@ L252-255 verbatim
/-- A static component of a lexicographic comparison decides by itself, unless
the two values are equal. -/
noncomputable def natLexF (a b : ℕ) (φ : transOrd.Formula α) : transOrd.Formula α :=
  if a < b then ⊤ else if b < a then ⊥ else φ


-- @@ L257-257 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A] {V : α → A}


-- @@ L259-261 verbatim
theorem realize_varF {v : QVarTag} {p q : α} :
    (varF v p q).Realize V ↔ QVarOn v (V p) (V q) := by
  cases v <;> simp [varF, QVarOn]


-- @@ L263-269 verbatim
theorem realize_allF {v : QVarTag} {p q : α} :
    (allF v p q).Realize V ↔ (v = .sB ∧ QVarOn v (V p) (V q)) := by
  rw [allF]
  split_ifs with h
  · rw [realize_varF]
    simp [h]
  · simp [h]


-- @@ L271-273 verbatim
theorem realize_clF {c : QClTag} {p q : α} :
    (clF c p q).Realize V ↔ QClOn c (V p) (V q) := by
  cases c <;> simp [clF, QClOn]


-- @@ L275-284 verbatim
theorem realize_natLexF {a b : ℕ} {φ : transOrd.Formula α} {P : Prop} (h : φ.Realize V ↔ P) :
    (natLexF a b φ).Realize V ↔ (a < b ∨ (a = b ∧ P)) := by
  rw [natLexF]
  split_ifs with h1 h2
  · simp [h1]
  · refine iff_of_false (by simp) ?_
    rintro (h3 | ⟨h3, -⟩) <;> omega
  · rw [h]
    have hab : a = b := by omega
    simp [hab]


-- @@ L286-286 verbatim
end Formulas


-- @@ L288-288 verbatim
/-! ### The coordinates of a two-argument defining formula -/


-- @@ L290-291 verbatim
/-- The first coordinate of the first argument. -/
abbrev x₀ : Fin 2 × Fin 2 := (0, 0)


-- @@ L293-294 verbatim
/-- The second coordinate of the first argument. -/
abbrev y₀ : Fin 2 × Fin 2 := (0, 1)


-- @@ L296-297 verbatim
/-- The first coordinate of the second argument. -/
abbrev x₁ : Fin 2 × Fin 2 := (1, 0)


-- @@ L299-300 verbatim
/-- The second coordinate of the second argument. -/
abbrev y₁ : Fin 2 × Fin 2 := (1, 1)


-- @@ L302-312 verbatim
/-- Where a literal's variable sits, as a formula in the four coordinates. -/
noncomputable def linkF : QLink → transOrd.Formula (Fin 2 × Fin 2)
  | .atP => eqF x₁ x₀ ⊓ isBotF y₁
  | .atQ => eqF x₁ y₀ ⊓ isBotF y₁
  | .botBoth => isBotF x₁ ⊓ isBotF y₁
  | .maxAtP => maxSVF x₁ ⊓ eqF y₁ x₀
  | .same => eqF x₁ x₀ ⊓ eqF y₁ y₀
  | .minAtQ => minSVF x₀ ⊓ eqF x₁ y₀ ⊓ isBotF y₁
  | .predAtQ => predSVF x₁ x₀ ⊓ eqF y₁ y₀
  | .occPos => posF x₀ x₁ ⊓ isBotF y₁
  | .occNeg => negF x₀ x₁ ⊓ isBotF y₁


-- @@ L314-317 verbatim
theorem realize_linkF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {k : QLink} {V : Fin 2 × Fin 2 → A} :
    (linkF k).Realize V ↔ LinkOn k (V x₀) (V y₀) (V x₁) (V y₁) := by
  cases k <;> simp [linkF, LinkOn, and_assoc]


-- @@ L319-324 verbatim
/-- **The occurrence formula**: the literals of the clause tag `ct` that are on
the variable tag `vt` with the sign `sgn`, gathered into a disjunction. -/
noncomputable def occF (sgn : Bool) (ct : QClTag) (vt : QVarTag) :
    transOrd.Formula (Fin 2 × Fin 2) :=
  listSup ((qLits ct).map fun l =>
    if l.vt = vt ∧ l.sign = sgn then clF ct x₀ y₀ ⊓ varF vt x₁ y₁ ⊓ linkF l.link else ⊥)


-- @@ L326-347 verbatim
theorem realize_occF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {sgn : Bool} {ct : QClTag} {vt : QVarTag} {V : Fin 2 × Fin 2 → A} :
    (occF sgn ct vt).Realize V ↔
      ∃ l ∈ qLits ct, l.vt = vt ∧ l.sign = sgn ∧
        QClOn ct (V x₀) (V y₀) ∧ QVarOn vt (V x₁) (V y₁) ∧
          LinkOn l.link (V x₀) (V y₀) (V x₁) (V y₁) := by
  classical
  rw [occF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hψmem
    by_cases hc : l.vt = vt ∧ l.sign = sgn
    · rw [ite_eq_left hc, Formula.realize_inf, Formula.realize_inf, realize_linkF, realize_clF,
        realize_varF] at hψ
      exact ⟨l, hl, hc.1, hc.2, hψ.1.1, hψ.1.2, hψ.2⟩
    · rw [ite_eq_right hc] at hψ
      exact hψ.elim
  · rintro ⟨l, hl, h1, h2, h3, h4, h5⟩
    refine ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
    rw [ite_eq_left ⟨h1, h2⟩, Formula.realize_inf, Formula.realize_inf, realize_linkF, realize_clF,
      realize_varF]
    exact ⟨⟨h3, h4⟩, h5⟩


-- @@ L349-349 verbatim
/-! ### The prefix formula -/


-- @@ L351-356 verbatim
/-- The lexicographic comparison of two keys, spelled out: the static
components decide by themselves, the two dynamic ones by an order atom. -/
def KeyLtRaw {A : Type} [LinearOrder A] (g : ℕ) (l : A) (s : ℕ) (c : A) (o : ℕ)
    (g' : ℕ) (l' : A) (s' : ℕ) (c' : A) (o' : ℕ) : Prop :=
  g < g' ∨ (g = g' ∧ (l < l' ∨ (l = l' ∧
    (s < s' ∨ (s = s' ∧ (c < c' ∨ (c = c' ∧ o < o')))))))


-- @@ L358-363 verbatim
theorem keyLt_iff_raw {A : Type} [LinearOrder A] (v v' : QVarTag) (p q p' q' : A) :
    KeyLt v p q v' p' q' ↔
      KeyLtRaw (keyGrp v) (keyLev v p q) (keySlot v) (keySec v p q) (keyOrd v)
        (keyGrp v') (keyLev v' p' q') (keySlot v') (keySec v' p' q') (keyOrd v') := by
  simp only [KeyLt, KeyLtRaw, TripleLt, keyTriple, Prod.mk.injEq]
  tauto


-- @@ L365-371 verbatim
/-- The body of the prefix comparison, with the four coordinates selected. -/
noncomputable def keyBodyF (v v' : QVarTag) (lv sc lv' sc' : Fin 2 × Fin 2) :
    transOrd.Formula (Fin 2 × Fin 2) :=
  natLexF (keyGrp v) (keyGrp v')
    (ltF lv lv' ⊔ (eqF lv lv' ⊓
      natLexF (keySlot v) (keySlot v')
        (ltF sc sc' ⊔ (eqF sc sc' ⊓ natLexF (keyOrd v) (keyOrd v') ⊥))))


-- @@ L373-394 verbatim
theorem realize_keyBodyF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {v v' : QVarTag} {lv sc lv' sc' : Fin 2 × Fin 2} {V : Fin 2 × Fin 2 → A} :
    (keyBodyF v v' lv sc lv' sc').Realize V ↔
      KeyLtRaw (keyGrp v) (V lv) (keySlot v) (V sc) (keyOrd v)
        (keyGrp v') (V lv') (keySlot v') (V sc') (keyOrd v') := by
  have hord : (natLexF (keyOrd v) (keyOrd v') (⊥ : transOrd.Formula (Fin 2 × Fin 2))).Realize V ↔
      keyOrd v < keyOrd v' := by
    rw [realize_natLexF (P := False) (by simp)]
    simp
  have hsec : (ltF sc sc' ⊔ (eqF sc sc' ⊓
      natLexF (keyOrd v) (keyOrd v') (⊥ : transOrd.Formula (Fin 2 × Fin 2)))).Realize V ↔
      (V sc < V sc' ∨ (V sc = V sc' ∧ keyOrd v < keyOrd v')) := by
    rw [Formula.realize_sup, Formula.realize_inf, realize_ltF, realize_eqF, hord]
  have hslot := realize_natLexF (V := V) (a := keySlot v) (b := keySlot v') hsec
  have hlev : (ltF lv lv' ⊔ (eqF lv lv' ⊓ natLexF (keySlot v) (keySlot v')
      (ltF sc sc' ⊔ (eqF sc sc' ⊓
        natLexF (keyOrd v) (keyOrd v') (⊥ : transOrd.Formula (Fin 2 × Fin 2)))))).Realize V ↔
      (V lv < V lv' ∨ (V lv = V lv' ∧
        (keySlot v < keySlot v' ∨ (keySlot v = keySlot v' ∧
          (V sc < V sc' ∨ (V sc = V sc' ∧ keyOrd v < keyOrd v')))))) := by
    rw [Formula.realize_sup, Formula.realize_inf, realize_ltF, realize_eqF, hslot]
  rw [keyBodyF, realize_natLexF hlev, KeyLtRaw]


-- @@ L396-401 verbatim
/-- **The quantifier prefix**, as a formula: both arguments are variables, and
their keys compare lexicographically. -/
noncomputable def prefF (v v' : QVarTag) : transOrd.Formula (Fin 2 × Fin 2) :=
  varF v x₀ y₀ ⊓ varF v' x₁ y₁ ⊓
    keyBodyF v v' (if levFst v then x₀ else y₀) (if levFst v then y₀ else x₀)
      (if levFst v' then x₁ else y₁) (if levFst v' then y₁ else x₁)


-- @@ L403-412 verbatim
theorem realize_prefF {A : Type} [Language.transSys.Structure A] [LinearOrder A]
    {v v' : QVarTag} {V : Fin 2 × Fin 2 → A} :
    (prefF v v').Realize V ↔
      QVarOn v (V x₀) (V y₀) ∧ QVarOn v' (V x₁) (V y₁) ∧
        KeyLt v (V x₀) (V y₀) v' (V x₁) (V y₁) := by
  rw [prefF, Formula.realize_inf, Formula.realize_inf, realize_keyBodyF, realize_varF,
    realize_varF, keyLt_iff_raw, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [keyLev, keySec]
  cases levFst v <;> cases levFst v' <;> simp


-- @@ L414-414 verbatim
end QsatRed


-- @@ L416-416 verbatim
open QsatRed


-- @@ L418-418 verbatim
/-! ### The interpretation -/


-- @@ L420-449 expanded
/-- **The Savitch interpretation**: the QSAT instance whose prefix and matrix
express reachability in the transition system described by the input, by
recursive doubling. -/
noncomputable def qsatInterp : FOInterpretation transOrd Language.qsat QTag 2 where
  relFormula {n}
    R :=
    match n, R with
    | _, .isVar => fun t =>
      match t 0 with
      | Sum.inl v => (varF v) (0, 0) (0, 1)
      | Sum.inr _ => ⊥
    | _, .allVar => fun t =>
      match t 0 with
      | Sum.inl v => (allF v) (0, 0) (0, 1)
      | Sum.inr _ => ⊥
    | _, .prefixLt => fun t =>
      match t 0, t 1 with
      | Sum.inl v, Sum.inl v' => prefF v v'
      | _, _ => ⊥
    | _, .isClause => fun t =>
      match t 0 with
      | Sum.inr c => (clF c) (0, 0) (0, 1)
      | Sum.inl _ => ⊥
    | _, .posIn => fun t =>
      match t 0, t 1 with
      | Sum.inr c, Sum.inl v => occF true c v
      | _, _ => ⊥
    | _, .negIn => fun t =>
      match t 0, t 1 with
      | Sum.inr c, Sum.inl v => occF false c v
      | _, _ => ⊥


-- @@ L451-451 verbatim
/-! ### Characterization of the interpreted relations -/


-- @@ L453-453 verbatim
section Characterizations


-- @@ L455-455 verbatim
variable {A : Type} [Language.transSys.Structure A] [LinearOrder A]


-- @@ L457-460 verbatim
/-- The universe of the constructed instance: a tag together with a pair of
elements of the input. -/
abbrev QM (A : Type) [Language.transSys.Structure A] [LinearOrder A] : Type :=
  (qsatInterp).Map A


-- @@ L462-463 verbatim
instance [Finite A] : Finite (QM A) :=
  inferInstanceAs (Finite (QTag × (Fin 2 → A)))


-- @@ L465-466 verbatim
instance [Nonempty A] : Nonempty (QM A) :=
  inferInstanceAs (Nonempty (QTag × (Fin 2 → A)))


-- @@ L468-471 verbatim
/-- **The variables**: the marked tagged pairs. -/
theorem qsat_isVar (v : QVarTag) (w : Fin 2 → A) :
    IsQVar (A := QM A) (Sum.inl v, w) ↔ QVarOn v (w 0) (w 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsIsVar ![(Sum.inl v, w)]) realize_varF


-- @@ L473-476 verbatim
/-- Elements carrying a clause tag are not variables. -/
theorem qsat_not_isVar (c : QClTag) (w : Fin 2 → A) :
    ¬IsQVar (A := QM A) (Sum.inr c, w) :=
  id


-- @@ L478-481 verbatim
/-- **The universal variables**: only the bits `b_ℓ`. -/
theorem qsat_isAll (v : QVarTag) (w : Fin 2 → A) :
    IsQAll (A := QM A) (Sum.inl v, w) ↔ (v = .sB ∧ QVarOn v (w 0) (w 1)) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsAllVar ![(Sum.inl v, w)]) realize_allF


-- @@ L483-486 verbatim
/-- Elements carrying a clause tag are not universal. -/
theorem qsat_not_isAll_cl (c : QClTag) (w : Fin 2 → A) :
    ¬IsQAll (A := QM A) (Sum.inr c, w) :=
  id


-- @@ L488-491 verbatim
/-- **The clauses**: the guarded tagged pairs. -/
theorem qsat_isClause (c : QClTag) (w : Fin 2 → A) :
    RelMap (M := QM A) qsIsClause ![(Sum.inr c, w)] ↔ QClOn c (w 0) (w 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsIsClause ![(Sum.inr c, w)]) realize_clF


-- @@ L493-496 verbatim
/-- Elements carrying a variable tag are not clauses. -/
theorem qsat_not_isClause (v : QVarTag) (w : Fin 2 → A) :
    ¬RelMap (M := QM A) qsIsClause ![(Sum.inl v, w)] :=
  id


-- @@ L498-504 verbatim
/-- **The prefix order** relates two variables exactly as their keys compare. -/
theorem qsat_prec (v v' : QVarTag) (w w' : Fin 2 → A) :
    QPrec (A := QM A) (Sum.inl v, w) (Sum.inl v', w') ↔
      QVarOn v (w 0) (w 1) ∧ QVarOn v' (w' 0) (w' 1) ∧
        KeyLt v (w 0) (w 1) v' (w' 0) (w' 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsPrefixLt
    ![(Sum.inl v, w), (Sum.inl v', w')]) realize_prefF


-- @@ L506-510 verbatim
/-- The prefix order does not relate a clause on the left. -/
theorem qsat_not_prec_left (c : QClTag) (x : QM A) (w : Fin 2 → A) :
    ¬QPrec (A := QM A) (Sum.inr c, w) x := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id


-- @@ L512-516 verbatim
/-- The prefix order does not relate a clause on the right. -/
theorem qsat_not_prec_right (c : QClTag) (x : QM A) (w : Fin 2 → A) :
    ¬QPrec (A := QM A) x (Sum.inr c, w) := by
  obtain ⟨t, u⟩ := x
  cases t <;> exact id


-- @@ L518-527 verbatim
/-- **The positive literals** of a clause: the literals of its list that are on
the given variable tag with a positive sign, and whose link pins that variable's
coordinates. -/
theorem qsat_posIn (c : QClTag) (v : QVarTag) (w y : Fin 2 → A) :
    RelMap (M := QM A) qsPosIn ![(Sum.inr c, w), (Sum.inl v, y)] ↔
      ∃ l ∈ qLits c, l.vt = v ∧ l.sign = true ∧
        QClOn c (w 0) (w 1) ∧ QVarOn v (y 0) (y 1) ∧
          LinkOn l.link (w 0) (w 1) (y 0) (y 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsPosIn
    ![(Sum.inr c, w), (Sum.inl v, y)]) realize_occF


-- @@ L529-536 verbatim
/-- **The negative literals** of a clause. -/
theorem qsat_negIn (c : QClTag) (v : QVarTag) (w y : Fin 2 → A) :
    RelMap (M := QM A) qsNegIn ![(Sum.inr c, w), (Sum.inl v, y)] ↔
      ∃ l ∈ qLits c, l.vt = v ∧ l.sign = false ∧
        QClOn c (w 0) (w 1) ∧ QVarOn v (y 0) (y 1) ∧
          LinkOn l.link (w 0) (w 1) (y 0) (y 1) :=
  Iff.trans (FOInterpretation.relMap_map qsatInterp A qsNegIn
    ![(Sum.inr c, w), (Sum.inl v, y)]) realize_occF


-- @@ L538-538 verbatim
end Characterizations


-- @@ L540-540 verbatim
end DescriptiveComplexity
