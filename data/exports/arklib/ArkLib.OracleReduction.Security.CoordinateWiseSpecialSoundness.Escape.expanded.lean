/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded


-- @@ L10-53 verbatim
/-!
  # Escape-aware CWSS packages and the package lattice

  Some reductions cannot always extract a witness: instead their extraction exhibits a
  cryptographic **escape**, e.g. a binding break of a commitment introduced mid-chain (Hachi's
  `w̃`-commitment of Figure 4, whose collision is a Module-SIS solution by weak binding,
  [NOZ26] Remark 2 / Lemma 7). An escape is an **event on the observable data** `(stmtIn, tree)`
  (`ChallengeTree.EscapeEvent`) entering the certificate as a disjunct of its conclusion:

  ```
  ∀ stmt tree, IsStructured → IsAccepting → esc stmt tree ∨ (stmt, Ext stmt tree) ∈ relIn
  ```

  Relations, witness types and extractors therefore stay plain; `esc` is the only escape-specific
  field a package carries. Since `esc` never mentions the extractor, no choice of extractor can
  discharge a certificate vacuously — the certificate is exactly as strong as its event is honest.
  `esc` is a **trusted specification**, on the same footing as `relIn`/`relOut`; its contract is
  stated once, on `ProtocolSpec.ChallengeTree.EscapeEvent`. Read it before writing an event.

  Packages carry their extraction algorithm as an explicit `extractor` field, so a composed chain
  exposes an actual end-to-end extractor `chain.extractor` — the algorithm a later knowledge-error
  accounting must run against the escape probability.

  ## The package lattice

  `CWSSPackage`, `EscapeCWSSPackage`, `GCWSSPackage`, `EscapeGCWSSPackage` form the 2×2 lattice
  escape? × guarded?, ordered by two **lossless** lifts: `toEscape` (at the never-firing event
  `fun _ _ => False`, so extractor and certificate are unchanged) and `toGuarded` (at the
  trivially-true check). A package is declared in the weakest corner it honestly lives in, and
  every ordered pair composes at the join through the universal `▷` — one scoped elaborator
  dispatching on the factors' package kinds (`▷ᵍ`, `▷ₑ`, `▷ₑᵍ` remain as explicit synonyms).

  Composition identifies only the relation seam `hRel`: escape events are combined by
  `ChallengeTree.EscapeEvent.append`, so factors tracking breaks of entirely different assumptions
  compose freely. Two pure packages compose on the pure append theorem; a genuinely guarded factor
  moves the composite — visibly in its type — onto the guarded one. A composed event reads the left
  verdict map off `L₁.isPure.verify` / `L₁.isGuarded.out`, i.e. off *data*, which is what keeps a
  composed chain's extractor computable.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/


-- @@ L55-55 verbatim
@[expose] public section



-- @@ L58-58 verbatim
open OracleComp OracleSpec ProtocolSpec


-- @@ L60-60 verbatim
namespace CoordinateWise


-- @@ L62-62 verbatim
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}


-- @@ L64-70 verbatim
/-! ## The escape-aware packages

The top half of the lattice: `EscapeCWSSPackage` and `EscapeGCWSSPackage` are `CWSSPackage` /
`GCWSSPackage` with one extra field, the escape event `esc`. `ChallengeTree.EscapeEvent.append`
takes the left verdict map as its index, and the packages carry that map as *data*, so a composed
`esc` reads `L₁.isPure.verify` (resp. `L₁.isGuarded.out`) rather than laundering it out of a `Prop`
with `Classical.choice`. -/


-- @@ L72-72 verbatim
section CanonicalEscapePackage


-- @@ L74-74 verbatim
variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}


-- @@ L76-89 verbatim
/-- A **bundled escape-aware coordinate-wise-special-sound reduction**: `CWSSPackage` with one extra
field, the **escape event** `esc`. Its certificate `isCWSS` concludes `esc stmt tree ∨ extraction
succeeds` on every structured accepting tree, so `relIn`/`relOut` and `extractor` stay ordinary.

`esc` is a trusted specification — reading its definition is the reader's obligation, just as for
`relIn`/`relOut` (contract: `ChallengeTree.EscapeEvent`). -/
structure EscapeCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier. -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The input relation. -/
  relIn : Set (StmtIn × WitIn)
  
-- @@ L90-91 verbatim
/-- The output relation. -/
  relOut : Set (StmtOut × WitOut)
  
-- @@ L92-94 verbatim
/-- The **escape event**: the cryptographic failure this package's extraction may exhibit
  instead of a witness. A trusted spec — see `ChallengeTree.EscapeEvent`. -/
  esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape struct).arity
  
-- @@ L95-97 verbatim
/-- The verifier is pure, **with its verdict function as data**: composition reads that function
  both for the composed extractor and for the composed escape event. -/
  isPure : verifier.PureForm
  
-- @@ L98-99 verbatim
/-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape struct).arity
  
-- @@ L100-103 verbatim
/-- The certificate: on every structured accepting tree, either the tree exhibits the escape
  event `esc`, or `extractor` succeeds on every valid leaf witnessing. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWithEscape init impl struct esc
    relIn relOut verifier extractor


-- @@ L105-114 verbatim
/-- A **guarded escape-aware CWSS package**: `EscapeCWSSPackage` with the purity witness relaxed to
a guardedness witness (the verifier may `failure` at runtime), again at the data form. -/
structure EscapeGCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier (which may reject at runtime). -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The input relation. -/
  relIn : Set (StmtIn × WitIn)
  
-- @@ L115-116 verbatim
/-- The output relation. -/
  relOut : Set (StmtOut × WitOut)
  
-- @@ L117-118 verbatim
/-- The **escape event**: a trusted spec (see `ChallengeTree.EscapeEvent`). -/
  esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape struct).arity
  
-- @@ L119-120 verbatim
/-- The verifier is guarded, **with its check and verdict map as data**. -/
  isGuarded : verifier.GuardedForm
  
-- @@ L121-122 verbatim
/-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape struct).arity
  
-- @@ L123-126 verbatim
/-- The certificate: on every structured accepting tree, either the tree exhibits the escape
  event `esc`, or `extractor` succeeds on every valid leaf witnessing. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWithEscape init impl struct esc
    relIn relOut verifier extractor


-- @@ L128-128 verbatim
/-! ### The canonical lattice lifts -/


-- @@ L130-130 verbatim
section CanonicalLift


-- @@ L132-132 verbatim
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}


-- @@ L134-145 verbatim
/-- Lift a pure escape-free package to the never-firing event; every other field carries over
unchanged. Lossless and computable. -/
def CWSSPackage.toEscape (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := fun _ _ => False
  isPure := L.isPure
  extractor := L.extractor
  isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ L.isCWSS


-- @@ L147-157 verbatim
/-- Lift a guarded escape-free package to the never-firing event. Lossless and computable. -/
def GCWSSPackage.toEscape (L : GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := fun _ _ => False
  isGuarded := L.isGuarded
  extractor := L.extractor
  isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ L.isCWSS


-- @@ L159-171 verbatim
/-- Regard a pure escape-aware package as guarded, at the trivially-true check, via
`Verifier.PureForm.toGuardedForm`. Lossless and computable. -/
def EscapeCWSSPackage.toGuarded
    (L : EscapeCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := L.esc
  isGuarded := L.isPure.toGuardedForm
  extractor := L.extractor
  isCWSS := L.isCWSS


-- @@ L173-173 verbatim
end CanonicalLift


-- @@ L175-180 verbatim
/-! ### The appends

The two same-kind escape-aware appends, then the ten mixed ones — each lifting its factors to the
join and delegating. The escape-free same-kind appends live in `Package.lean`
(`CWSSPackage.append`) and `Guarded.lean` (`GCWSSPackage.append`, `CWSSPackage.appendGuarded`,
`GCWSSPackage.appendPure`). -/


-- @@ L182-182 verbatim
section CanonicalAppend


-- @@ L184-186 verbatim
variable {StmtA WitA StmtB WitB StmtC WitC : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]


-- @@ L188-208 verbatim
/-- **Compose two escape-aware packages along a matching relation seam.** The composed event is
`ChallengeTree.EscapeEvent.append` at `L₁.isPure.verify` — the left verdict map as *data*, no choice
laundering — and the composed extractor is `Extractor.TreeBased.append` at the same map. -/
def EscapeCWSSPackage.append
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  esc := L₁.esc.append L₂.esc L₁.isPure.verify
  isPure := L₁.isPure.append L₂.isPure
  extractor := L₁.extractor.append L₁.isPure.verify L₂.extractor
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hRel] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWithEscape init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct L₁.esc L₂.esc
      L₁.isPure.verify L₁.isPure.verify_eq L₁.extractor L₂.extractor L₁.isCWSS h₂


-- @@ L210-235 verbatim
/-- **Compose two guarded escape-aware packages along a matching relation seam.** As in
`EscapeCWSSPackage.append`, but the event and the extractor are taken at the guard's output map
`L₁.isGuarded.out`, which `IsGuardedWith` leaves unconstrained on rejected prefixes — harmless,
since escape events must be honest at *all* `(stmt, tree)` pairs. The certificate is
`Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft`, its positivity hypothesis
discharged by `CWSSStructure.toShape_arity_pos`. -/
def EscapeGCWSSPackage.append
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  esc := L₁.esc.append L₂.esc L₁.isGuarded.out
  isGuarded := L₁.isGuarded.append L₂.isGuarded
  extractor := L₁.extractor.append L₁.isGuarded.out L₂.extractor
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hRel] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct
      L₁.isGuarded.check L₁.isGuarded.out L₁.isGuarded.verify_eq
      (CWSSStructure.toShape_arity_pos L₂.struct)
      L₁.esc L₂.esc L₁.extractor L₂.extractor L₁.isCWSS h₂


-- @@ L237-243 verbatim
/-- **Pure escape-free ▷ pure escape-aware.** Lifts the left factor. -/
def CWSSPackage.appendEscape
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂ hRel


-- @@ L245-251 verbatim
/-- **Pure escape-aware ▷ pure escape-free.** Lifts the right factor. -/
def EscapeCWSSPackage.appendPure
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toEscape hRel


-- @@ L253-259 verbatim
/-- **Pure escape-free ▷ guarded escape-aware.** Lifts the left factor twice. -/
def CWSSPackage.appendEscapeGuarded
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.toGuarded.append L₂ hRel


-- @@ L261-267 verbatim
/-- **Guarded escape-aware ▷ pure escape-free.** Lifts the right factor twice. -/
def EscapeGCWSSPackage.appendPure
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toEscape.toGuarded hRel


-- @@ L269-276 verbatim
/-- **Guarded escape-free ▷ pure escape-aware.** Lifts the left factor to the never-event and the
right factor to the trivially-true guard. -/
def GCWSSPackage.appendEscape
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂.toGuarded hRel


-- @@ L278-284 verbatim
/-- **Guarded escape-free ▷ guarded escape-aware.** Lifts the left factor to the never-event. -/
def GCWSSPackage.appendEscapeGuarded
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂ hRel


-- @@ L286-293 verbatim
/-- **Pure escape-aware ▷ guarded escape-free.** Lifts the left factor to the trivially-true guard
and the right factor to the never-event. -/
def EscapeCWSSPackage.appendGuarded
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂.toEscape hRel


-- @@ L295-302 verbatim
/-- **Pure escape-aware ▷ guarded escape-aware.** Lifts the left factor to the trivially-true guard;
both factors keep their own events. -/
def EscapeCWSSPackage.appendEscapeGuarded
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂ hRel


-- @@ L304-310 verbatim
/-- **Guarded escape-aware ▷ guarded escape-free.** Lifts the right factor to the never-event. -/
def EscapeGCWSSPackage.appendGuarded
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toEscape hRel


-- @@ L312-319 verbatim
/-- **Guarded escape-aware ▷ pure escape-aware.** Lifts the right factor to the trivially-true
guard; both factors keep their own events. -/
def EscapeGCWSSPackage.appendEscape
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toGuarded hRel


-- @@ L321-321 verbatim
end CanonicalAppend


-- @@ L323-323 verbatim
end CanonicalEscapePackage


-- @@ L325-326 verbatim
@[inherit_doc EscapeCWSSPackage.append]
scoped infixr:65 " ▷ₑ " => EscapeCWSSPackage.append


-- @@ L328-329 verbatim
@[inherit_doc EscapeGCWSSPackage.append]
scoped infixr:65 " ▷ₑᵍ " => EscapeGCWSSPackage.append


-- @@ L331-338 verbatim
/-! ### The universal append `▷`

A single (scoped) elaborator rather than sixteen overloaded notations: `L₁ ▷ L₂` elaborates both
factors once, reads the head constant of their types to determine the package kinds, and applies
the unique append that composes them at their join. Overloaded-notation `choice` nodes would
re-elaborate nested alternatives once per outer candidate — exponential in chain length, and a
five-link Hachi chain already exhausts the heartbeat budget — whereas this dispatch is linear.
The kind-marked infixes `▷ₑ`, `▷ᵍ`, `▷ₑᵍ` remain as single-target explicit synonyms. -/


-- @@ L340-340 verbatim
section UniversalAppend


-- @@ L342-342 verbatim
open Lean Elab Term Meta


-- @@ L344-363 verbatim
/-- The dispatch table of the universal append `▷` over the **canonical** package kinds: the two
factors' kinds determine the append that composes them at their join. -/
private meta def canonAppendFn : Name → Name → Option Name
  | ``CWSSPackage,        ``CWSSPackage        => some ``CWSSPackage.append
  | ``CWSSPackage,        ``EscapeCWSSPackage  => some ``CWSSPackage.appendEscape
  | ``CWSSPackage,        ``GCWSSPackage       => some ``CWSSPackage.appendGuarded
  | ``CWSSPackage,        ``EscapeGCWSSPackage => some ``CWSSPackage.appendEscapeGuarded
  | ``EscapeCWSSPackage,  ``CWSSPackage        => some ``EscapeCWSSPackage.appendPure
  | ``EscapeCWSSPackage,  ``EscapeCWSSPackage  => some ``EscapeCWSSPackage.append
  | ``EscapeCWSSPackage,  ``GCWSSPackage       => some ``EscapeCWSSPackage.appendGuarded
  | ``EscapeCWSSPackage,  ``EscapeGCWSSPackage => some ``EscapeCWSSPackage.appendEscapeGuarded
  | ``GCWSSPackage,       ``CWSSPackage        => some ``GCWSSPackage.appendPure
  | ``GCWSSPackage,       ``EscapeCWSSPackage  => some ``GCWSSPackage.appendEscape
  | ``GCWSSPackage,       ``GCWSSPackage       => some ``GCWSSPackage.append
  | ``GCWSSPackage,       ``EscapeGCWSSPackage => some ``GCWSSPackage.appendEscapeGuarded
  | ``EscapeGCWSSPackage, ``CWSSPackage        => some ``EscapeGCWSSPackage.appendPure
  | ``EscapeGCWSSPackage, ``EscapeCWSSPackage  => some ``EscapeGCWSSPackage.appendEscape
  | ``EscapeGCWSSPackage, ``GCWSSPackage       => some ``EscapeGCWSSPackage.appendGuarded
  | ``EscapeGCWSSPackage, ``EscapeGCWSSPackage => some ``EscapeGCWSSPackage.append
  | _,                    _                    => none


-- @@ L365-371 verbatim
/-- The package kind — the head constant of the type — of an elaborated `▷` factor. -/
private meta def packageKindOf (e : Expr) : TermElabM Name := do
  let t ← whnf (← instantiateMVars (← inferType e))
  match t.getAppFn.constName? with
  | some n => return n
  | none =>
    throwError "▷: cannot determine the package kind of{indentExpr e}\nof type{indentExpr t}"


-- @@ L373-377 verbatim
/-- Apply a named append to two elaborated factors. -/
private meta def applyAppend (fn : Name) (lE rE : Expr) : TermElabM Expr := do
  let f ← mkConstWithFreshMVarLevels fn
  elabAppArgs f #[] #[.expr lE, .expr rE] (expectedType? := none)
    (explicit := false) (ellipsis := false)


-- @@ L379-393 verbatim
/-- **The universal package append.** `L₁ ▷ L₂` composes any two CWSS packages — pure, guarded,
escape-aware, or both — at the join of their kinds, lifting each factor as needed. The relation
seam is discharged by `rfl`; for a non-definitional seam call the dispatched append (see
`canonAppendFn`) explicitly with the seam proof.

Dispatch is by kind, and deterministic: the two factors' kinds index `canonAppendFn`, the single
dispatch table. -/
scoped elab:65 l:term:66 " ▷ " r:term:65 : term => do
  let lE ← elabTerm l none
  let rE ← elabTerm r none
  let lN ← packageKindOf lE
  let rN ← packageKindOf rE
  let some fn := canonAppendFn lN rN
    | throwError "▷: no package append composes `{lN}` with `{rN}`"
  applyAppend fn lE rE


-- @@ L395-395 verbatim
end UniversalAppend


-- @@ L397-397 verbatim
end CoordinateWise
