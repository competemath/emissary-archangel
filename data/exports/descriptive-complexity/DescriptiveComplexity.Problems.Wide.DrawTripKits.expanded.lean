/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawTrip
import DescriptiveComplexity.Problems.Wide.DrawKit


-- @@ L9-33 verbatim
/-!
# Kits for the round trips: the file test

The kit wrapping the file-test round trip, by the template of
`DescriptiveComplexity.Problems.Wide.DrawKit`: a phase inductive, a rule
inductive with concrete guards, the rules function at a phase embedding, an
in-shape separation lemma, and a discharge – any program whose rule set
contains the kit's rules satisfies the composite's run theorem
(`DescriptiveComplexity.Draw.TestKit.reaches_pos`/`_neg`: scan up to the file
top, bounce, one question per register on the way down, verdict in the phase,
return to the marker).

The verdict phases double as return phases, which is where the cell-coupled
forms of the layer earn their keep: the walking rule of the passing phase is
guarded `rg ≠ one ∧ wk ≠ one`, disjoint from the register rules, and the
coupled hypotheses of `DescriptiveComplexity.Draw.Prog.reaches_fileRoundTrip` are
exactly what shows it fires wherever the composite needs it. The failing
phase hosts no register rule, so its single rule takes the disjunction
`rg = one ∨ wk ≠ one` and serves hold, walk and return at once.

Rules are owned by their source phase: how a program *enters* the kit (at the
scan phase, off the marker) and how it *leaves* the two verdict phases (at
the marker, guarded `wk = one ∧ rg ≠ one`, disjoint from every rule here) is
the caller's business.
-/


-- @@ L35-35 verbatim
namespace DescriptiveComplexity


-- @@ L37-37 verbatim
namespace Draw


-- @@ L39-39 verbatim
open FirstOrder


-- @@ L41-41 verbatim
open Language Structure


-- @@ L43-43 verbatim
/-! ### The file test's shapes -/


-- @@ L45-56 verbatim
/-- **The phases of a test trip**: the up-scan, the bounce, and the two
verdict phases – the passing one doubling as the descent phase of the pass. -/
inductive TestPh : Type
  /-- Scanning up to the file top. -/
  | up : TestPh
  /-- Bounced off the top, about to re-enter rightwards. -/
  | b2 : TestPh
  /-- Every register so far passed (also: returning with verdict *yes*). -/
  | ty : TestPh
  /-- Some register failed (also: returning with verdict *no*). -/
  | tn : TestPh
  deriving DecidableEq


-- @@ L58-62 verbatim
instance : Finite TestPh :=
  Finite.of_injective
    (fun p => match p with
      | .up => (0 : Fin 4) | .b2 => 1 | .ty => 2 | .tn => 3)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L64-80 verbatim
/-- **The rule families of a test trip**, one constructor each. -/
inductive TestRule : Type
  /-- Scan right while the file-top mark is clear. -/
  | up : TestRule
  /-- At the file top: step left into the bounce phase. -/
  | b1 : TestRule
  /-- Bounce: step back right into the pass. -/
  | b2go : TestRule
  /-- At a register that passes the question: carry on down. -/
  | pass : TestRule
  /-- At a register that fails it: switch to the failing phase. -/
  | fail : TestRule
  /-- Walk left over unmarked cells, and return, in the passing phase. -/
  | walkY : TestRule
  /-- Hold at registers, walk and return, in the failing phase. -/
  | stayN : TestRule
  deriving DecidableEq


-- @@ L82-87 verbatim
instance : Finite TestRule :=
  Finite.of_injective
    (fun p => match p with
      | .up => (0 : Fin 7) | .b1 => 1 | .b2go => 2 | .pass => 3 | .fail => 4
      | .walkY => 5 | .stayN => 6)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L89-104 verbatim
/-- **A file-test kit**: the walked track, the three service slots, the
per-register question as a predicate of the tracks, and where its phases sit
in the program. -/
structure TestKit (A Q W P : Type) where
  /-- The walked track being questioned. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The per-register question, decided by the tracks. -/
  TestG : (W → A) → Prop
  /-- The kit's phases in the program. -/
  emb : TestPh → P


-- @@ L106-106 verbatim
namespace TestKit


-- @@ L108-108 verbatim
variable {A Q W P : Type} (κ : TestKit A Q W P) (one : A)


-- @@ L110-160 verbatim
/-- **The kit's rules.** -/
def rule : TestRule → Rule A Q W P
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .up
      dstPh := κ.emb .b2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b2
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .pass =>
    { guard := fun _ g => κ.TestG g ∧ g κ.rg = one
      srcPh := κ.emb .ty
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .fail =>
    { guard := fun _ g => ¬κ.TestG g ∧ g κ.rg = one
      srcPh := κ.emb .ty
      dstPh := κ.emb .tn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .walkY =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .ty
      dstPh := κ.emb .ty
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stayN =>
    { guard := fun _ g => g κ.rg = one ∨ g κ.wk ≠ one
      srcPh := κ.emb .tn
      dstPh := κ.emb .tn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }


-- @@ L162-177 verbatim
/-- **In-shape separation**: two of the kit's rules firing in the same phase
on the same data are the same rule. -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TestRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg.1 hg'.1
    | exact absurd hg'.1 hg.1
    | exact absurd hg.2 hg'.1
    | exact absurd hg'.2 hg.1


-- @@ L179-192 verbatim
/-- **Exit disjointness**: at the kit's two verdict phases – where a caller's
exit rule, guarded `wk = one ∧ rg ≠ one`, lives – no kit rule fires on a
symbol satisfying that guard. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TestRule) (f : Q → A) (g : W → A), (κ.rule one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      ((κ.rule one ρ).srcPh = κ.emb .ty ∨ (κ.rule one ρ).srcPh = κ.emb .tn) →
      False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> rcases hph with hph | hph <;> first
    | exact absurd hg.2 hrg
    | exact absurd hwk hg.2
    | exact hg.elim (fun h1 => hrg h1) (fun h2 => h2 hwk)
    | (have hbb := hemb hph; cases hbb)


-- @@ L194-198 verbatim
/-- **The trip stays inside its own phases**: every rule lands in one the kit
was given, which is what a caller that must know a property of the phases the
machine can be in reads off a sub-machinery. -/
theorem dstPh_emb (ρ : TestRule) : ∃ p, (κ.rule one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩


-- @@ L200-200 verbatim
/-! ### The discharge -/


-- @@ L202-202 verbatim
section Discharge


-- @@ L204-204 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L205-205 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L206-206 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L207-207 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L208-208 verbatim
variable {PR : Prog A R P Q W K dd} {κ : TestKit A Q W P}

-- @@ L209-209 verbatim
variable {rEmb : TestRule → R}

-- @@ L210-210 verbatim
variable (hrules : ∀ ρ : TestRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)

-- @@ L211-211 verbatim
variable {I : Type} [Finite I] {ile : I → I → Prop}

-- @@ L212-212 verbatim
variable (F : IxFile (Univ A R P K dd) I ile)

-- @@ L213-213 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L214-214 verbatim
variable (hix : IsLinOrd ile)

-- @@ L215-215 verbatim
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)

-- @@ L216-216 verbatim
variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)

-- @@ L217-217 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}

-- @@ L218-218 verbatim
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (F.cell gbot))

-- @@ L219-220 verbatim
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))

-- @@ L221-222 verbatim
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))

-- @@ L223-224 verbatim
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))

-- @@ L225-225 verbatim
variable {Test : I → Prop}

-- @@ L226-227 verbatim
variable (hcompat : ∀ u : I,
  κ.TestG (PR.passTracksAt F.cell κ.t rest m (F.cell u)) ↔ Test u)

-- @@ L228-228 verbatim
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

-- @@ L229-229 verbatim
variable (hsle : WMSetLe WMLe s (F.cell gtop))

-- @@ L230-231 verbatim
variable {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ w)


-- @@ L233-256 verbatim
omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness. -/
private theorem has_of_rule {ρ : TestRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.one ρ).guard f g)
    (hkeepSt : (κ.rule PR.one ρ).dstSt f g = f)
    (hkeepWr : (κ.rule PR.one ρ).wr f g = g) :
    (∀ _hmr : (κ.rule PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh f g) ∧
    (∀ _hml : ¬(κ.rule PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh f g) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules]; exact hkeepSt, by rw [hrules]; exact hkeepWr,
      by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules]; exact hkeepSt, by rw [hrules]; exact hkeepWr,
      fun hc => hml (by rw [hrules] at hc; exact hc)⟩


-- @@ L258-276 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite I] in
include F hlin hix hnewk hbot hwkLt hwkS in
/-- The marker slot is clear at or above the register file. -/
private theorem wkOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : I, WMSetLe WMLe (F.cell x) r) :
    PR.passTracksAt F.cell κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
        ⟨hbot x, fun hc => hne (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one


-- @@ L278-287 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Finite I] in
include F hnerg hrg in
/-- The register mark is clear at unmarked cells. -/
private theorem rgOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hno : ∀ x : I, r ≠ F.cell x) :
    PR.passTracksAt F.cell κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one


-- @@ L289-315 verbatim
include hrules F hR hlin hix hnerg hnewk htop hbot hwkLt hrg hwkS hcompat hgap in
/-- The pass down the file, verdict in the state. -/
private theorem test_partIn :
    ∃ q : Univ A R P K dd → Prop, WMIncr WMLe q (F.cell gbot) ∧
      (wideData (Univ A R P K dd)).ReachesIn ((ixRank ile gtop - ixRank ile gbot) * w + 1)
        ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl (F.cell gtop),
          wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
        ⟨Sum.inr (accStateAfter ile Test (PR.stElt (κ.emb .ty) fc)
            (PR.stElt (κ.emb .tn) fc) gbot), Sum.inl q,
          wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  Prog.reachesIn_fileTestG F (Test := Test) (TestG := κ.TestG)
    hR hlin hix (m := m) (t := κ.t) (rg := κ.rg) hnerg (rest := rest) hrg hcompat
    (py := κ.emb .ty) (pn := κ.emb .tn) (f := fc)
    (fun _g hT hg1 =>
      (has_of_rule hrules (ρ := .pass) ⟨hT, hg1⟩ rfl rfl).2 not_false)
    (fun _g hT hg1 =>
      (has_of_rule hrules (ρ := .fail) ⟨hT, hg1⟩ rfl rfl).2 not_false)
    (fun _g hg1 =>
      (has_of_rule hrules (ρ := .stayN) (Or.inl hg1) rfl rfl).2 not_false)
    (fun r hbnd hno =>
      (has_of_rule hrules (ρ := .walkY)
        ⟨rgOff F hnerg hrg m r hno, wkOff F hlin hix hnewk hbot hwkLt hwkS m r hbnd⟩
        rfl rfl).2 not_false)
    (fun r hbnd _hno =>
      (has_of_rule hrules (ρ := .stayN)
        (Or.inr (wkOff F hlin hix hnewk hbot hwkLt hwkS m r hbnd)) rfl rfl).2 not_false)
    (w := w) hgap (top := gtop) (bot := gbot) htop hbot


-- @@ L317-349 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat hsle hgap in
/-- **The kit runs a passing file test**: from the scan phase anywhere, up to
the file top, down the file – every register passing – and back to the marker
in the passing phase. -/
theorem reachesIn_pos (hTest : ∀ u, Test u) :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + 2 + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot))
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, htest⟩ := test_partIn hrules F hR hlin hix hnerg hnewk htop hbot
    hwkLt hrg hwkS hcompat hgap (fc := fc)
  rw [accStateAfter_bot_pos hTest] at htest
  refine (Prog.reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := rest)
    (m := m) (m₂ := m) (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .ty) (pOut := κ.emb .ty) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg rfl rfl).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t rest m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)
      rfl rfl).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial rfl rfl).1 trivial)
    hq htest
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walkY)
        ⟨rgOff F hnerg hrg m r hno, hwk⟩ rfl rfl).2 not_false)
    hwkLt hsle).mono (by
    have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
    have h₂ : wideRank q - wideRank wkAddr ≤ wideRank (F.cell gbot) :=
      le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
    omega)


-- @@ L351-362 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat hsle in
/-- **The kit runs a passing file test**, the budget forgotten. -/
theorem reaches_pos (hTest : ∀ u, Test u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ty) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_pos hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat hsle
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))
    hTest).reflTransGen


-- @@ L364-394 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat hsle hgap in
/-- **The kit runs a failing file test**: some register fails, and the trip
ends at the marker in the failing phase. -/
theorem reachesIn_neg {u : I} (hTest : ¬Test u) :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + 2 + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot))
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .tn) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, htest⟩ := test_partIn hrules F hR hlin hix hnerg hnewk htop hbot
    hwkLt hrg hwkS hcompat hgap (fc := fc)
  rw [accStateAfter_bot_neg hbot hTest] at htest
  refine (Prog.reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := rest)
    (m := m) (m₂ := m) (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .ty) (pOut := κ.emb .tn) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg rfl rfl).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t rest m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)
      rfl rfl).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial rfl rfl).1 trivial)
    hq htest
    (fun r _hno hwk =>
      (has_of_rule hrules (ρ := .stayN) (Or.inr hwk) rfl rfl).2 not_false)
    hwkLt hsle).mono (by
    have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
    have h₂ : wideRank q - wideRank wkAddr ≤ wideRank (F.cell gbot) :=
      le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
    omega)


-- @@ L396-407 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat hsle in
/-- **The kit runs a failing file test**, the budget forgotten. -/
theorem reaches_neg {u : I} (hTest : ¬Test u) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .tn) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_neg hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hcompat hsle
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))
    hTest).reflTransGen


-- @@ L409-409 verbatim
end Discharge


-- @@ L411-411 verbatim
end TestKit


-- @@ L413-418 verbatim
/-! ### The clear and copy trips

The same itinerary with a writing pass in the middle: one phase runs the
descent and the return alike, its register rule rewriting the walked digit
and its walking rule – guarded `rg ≠ one ∧ wk ≠ one` – serving the gaps of
the file and the way home. -/


-- @@ L420-429 verbatim
/-- **The phases of a write-pass trip**: the up-scan, the bounce, and the one
pass-and-return phase. -/
inductive TrackPh : Type
  /-- Scanning up to the file top. -/
  | up : TrackPh
  /-- Bounced off the top, about to re-enter rightwards. -/
  | b2 : TrackPh
  /-- Running the pass down the file, and returning. -/
  | run : TrackPh
  deriving DecidableEq


-- @@ L431-434 verbatim
instance : Finite TrackPh :=
  Finite.of_injective
    (fun p => match p with | .up => (0 : Fin 3) | .b2 => 1 | .run => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L436-448 verbatim
/-- **The rule families of a write-pass trip.** -/
inductive TrackRule : Type
  /-- Scan right while the file-top mark is clear. -/
  | up : TrackRule
  /-- At the file top: step left into the bounce phase. -/
  | b1 : TrackRule
  /-- Bounce: step back right into the pass. -/
  | b2go : TrackRule
  /-- At a register: rewrite the walked digit and carry on down. -/
  | put : TrackRule
  /-- Walk left over unmarked cells, and return. -/
  | walk : TrackRule
  deriving DecidableEq


-- @@ L450-454 verbatim
instance : Finite TrackRule :=
  Finite.of_injective
    (fun p => match p with
      | .up => (0 : Fin 5) | .b1 => 1 | .b2go => 2 | .put => 3 | .walk => 4)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L456-468 verbatim
/-- **A track-clearing kit**: the walked track, the three service slots, and
the phases. -/
structure ClearKit (A Q W P : Type) where
  /-- The walked track being cleared. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : TrackPh → P


-- @@ L470-470 verbatim
namespace ClearKit


-- @@ L472-472 verbatim
variable {A Q W P : Type} [DecidableEq W] (κ : ClearKit A Q W P) (zero one : A)


-- @@ L474-510 verbatim
/-- **The kit's rules.** -/
def rule : TrackRule → Rule A Q W P
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .up
      dstPh := κ.emb .b2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b2
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun _ g => g κ.rg = one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t zero
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }


-- @@ L512-516 verbatim
/-- **The trip stays inside its own phases**: every rule lands in one the kit
was given, which is what a caller that must know a property of the phases the
machine can be in reads off a sub-machinery. -/
theorem dstPh_emb (ρ : TrackRule) : ∃ p, (κ.rule zero one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩


-- @@ L518-530 verbatim
/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TrackRule) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg hg'.1
    | exact absurd hg' hg.1


-- @@ L532-541 verbatim
/-- **Exit disjointness** at the kit's pass-and-return phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TrackRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb .run → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)


-- @@ L543-543 verbatim
section Discharge


-- @@ L545-545 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L546-546 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L547-547 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L548-548 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L549-549 verbatim
variable {PR : Prog A R P Q W K dd} {κ : ClearKit A Q W P}

-- @@ L550-550 verbatim
variable {rEmb : TrackRule → R}

-- @@ L551-551 verbatim
variable (hrules : ∀ ρ : TrackRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)

-- @@ L552-552 verbatim
variable {I : Type} [Finite I] {ile : I → I → Prop}

-- @@ L553-553 verbatim
variable (F : IxFile (Univ A R P K dd) I ile)

-- @@ L554-554 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L555-555 verbatim
variable (hix : IsLinOrd ile)

-- @@ L556-556 verbatim
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)

-- @@ L557-557 verbatim
variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)

-- @@ L558-558 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}

-- @@ L559-559 verbatim
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (F.cell gbot))

-- @@ L560-561 verbatim
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))

-- @@ L562-563 verbatim
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))

-- @@ L564-565 verbatim
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))

-- @@ L566-566 verbatim
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

-- @@ L567-567 verbatim
variable (hsle : WMSetLe WMLe s (F.cell gtop))

-- @@ L568-569 verbatim
variable {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ w)


-- @@ L571-593 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : TrackRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.zero PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩


-- @@ L595-612 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite I] in
include F hlin hix hnewk hbot hwkLt hwkS in
private theorem wkOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : I, WMSetLe WMLe (F.cell x) r) :
    PR.passTracksAt F.cell κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
        ⟨hbot x, fun hc => hne (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one


-- @@ L614-622 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Finite I] in
include F hnerg hrg in
private theorem rgOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hno : ∀ x : I, r ≠ F.cell x) :
    PR.passTracksAt F.cell κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one


-- @@ L624-659 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hsle hgap in
/-- **The kit clears its track**: from the scan phase anywhere, up to the file
top, one pass writing the clear digit at every register, and back to the
marker. -/
theorem reachesIn :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + 2 + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot))
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest fun _ => False) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hpass⟩ := Prog.reachesIn_fileClearTrack F hR hlin hix (t := κ.t) (rg := κ.rg)
    hnerg (rest := rest) hrg (m := m) (p := κ.emb .run) (f := fc)
    (fun _g hg1 => (has_of_rule hrules (ρ := .put) hg1).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff F hnerg hrg k r hno, wkOff F hlin hix hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (w := w) hgap (top := gtop) (bot := gbot) htop hbot
  refine (Prog.reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := rest)
    (m := m) (m₂ := fun _ => False) (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .run) (pOut := κ.emb .run) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t rest m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hq hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walk) ⟨rgOff F hnerg hrg _ r hno, hwk⟩).2 not_false)
    hwkLt hsle).mono (by
    have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
    have h₂ : wideRank q - wideRank wkAddr ≤ wideRank (F.cell gbot) :=
      le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
    omega)


-- @@ L661-671 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hsle in
/-- **The kit clears a track**, the budget forgotten. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest fun _ => False) (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hsle
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))).reflTransGen


-- @@ L673-673 verbatim
end Discharge


-- @@ L675-675 verbatim
end ClearKit


-- @@ L677-691 verbatim
/-- **A track-copying kit**: the walked track, the source slot – which must
hold a bit at every register – the three service slots, and the phases. -/
structure CopyKit (A Q W P : Type) where
  /-- The walked track being overwritten. -/
  t : W
  /-- The source slot whose digit is copied. -/
  src : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The kit's phases in the program. -/
  emb : TrackPh → P


-- @@ L693-693 verbatim
namespace CopyKit


-- @@ L695-695 verbatim
variable {A Q W P : Type} [DecidableEq W] (κ : CopyKit A Q W P) (one : A)


-- @@ L697-733 verbatim
/-- **The kit's rules.** -/
def rule : TrackRule → Rule A Q W P
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .up
      dstPh := κ.emb .b2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b2
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun _ g => g κ.rg = one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t (g κ.src)
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }


-- @@ L735-739 verbatim
/-- **The trip stays inside its own phases**: every rule lands in one the kit
was given, which is what a caller that must know a property of the phases the
machine can be in reads off a sub-machinery. -/
theorem dstPh_emb (ρ : TrackRule) : ∃ p, (κ.rule one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩


-- @@ L741-753 verbatim
/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TrackRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg hg'.1
    | exact absurd hg' hg.1


-- @@ L755-764 verbatim
/-- **Exit disjointness** at the kit's pass-and-return phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TrackRule) (f : Q → A) (g : W → A), (κ.rule one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule one ρ).srcPh = κ.emb .run → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)


-- @@ L766-766 verbatim
section Discharge


-- @@ L768-768 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L769-769 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L770-770 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L771-771 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L772-772 verbatim
variable {PR : Prog A R P Q W K dd} {κ : CopyKit A Q W P}

-- @@ L773-773 verbatim
variable {rEmb : TrackRule → R}

-- @@ L774-774 verbatim
variable (hrules : ∀ ρ : TrackRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)

-- @@ L775-775 verbatim
variable {I : Type} [Finite I] {ile : I → I → Prop}

-- @@ L776-776 verbatim
variable (F : IxFile (Univ A R P K dd) I ile)

-- @@ L777-777 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L778-778 verbatim
variable (hix : IsLinOrd ile)

-- @@ L779-779 verbatim
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)

-- @@ L780-780 verbatim
variable (hnesrc : κ.src ≠ κ.t)

-- @@ L781-781 verbatim
variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)

-- @@ L782-782 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}

-- @@ L783-783 verbatim
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (F.cell gbot))

-- @@ L784-785 verbatim
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))

-- @@ L786-787 verbatim
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))

-- @@ L788-789 verbatim
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))

-- @@ L790-791 verbatim
variable (hsrcBit : ∀ u : I,
  rest (F.cell u) κ.src = PR.zero ∨ rest (F.cell u) κ.src = PR.one)

-- @@ L792-792 verbatim
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

-- @@ L793-793 verbatim
variable (hsle : WMSetLe WMLe s (F.cell gtop))

-- @@ L794-795 verbatim
variable {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ w)


-- @@ L797-819 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : TrackRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.one ρ).srcPh f g
        (κ.rule PR.one ρ).dstPh ((κ.rule PR.one ρ).dstSt f g)
        ((κ.rule PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩


-- @@ L821-838 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite I] in
include F hlin hix hnewk hbot hwkLt hwkS in
private theorem wkOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : I, WMSetLe WMLe (F.cell x) r) :
    PR.passTracksAt F.cell κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
        ⟨hbot x, fun hc => hne (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one


-- @@ L840-848 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Finite I] in
include F hnerg hrg in
private theorem rgOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hno : ∀ x : I, r ≠ F.cell x) :
    PR.passTracksAt F.cell κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one


-- @@ L850-889 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk hnesrc htop hbot hwkLt hrg hrl hwkS hsrcBit hsle
  hgap in
/-- **The kit copies the source slot into its track**: from the scan phase
anywhere, up to the file top, one pass replacing every register's walked digit
by its source digit, and back to the marker. -/
theorem reachesIn :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + 2 + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot))
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest fun u => rest (F.cell u) κ.src = PR.one)
          (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hpass⟩ := Prog.reachesIn_fileCopyTrack F hR hlin hix (t := κ.t) (rg := κ.rg)
    (src := κ.src) hnerg hnesrc (rest := rest) hrg hsrcBit (m := m)
    (p := κ.emb .run) (f := fc)
    (fun _g hg1 => (has_of_rule hrules (ρ := .put) hg1).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff F hnerg hrg k r hno, wkOff F hlin hix hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (w := w) hgap (top := gtop) (bot := gbot) htop hbot
  refine (Prog.reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := rest)
    (m := m) (m₂ := fun u => rest (F.cell u) κ.src = PR.one) (wkAddr := wkAddr)
    hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .run) (pOut := κ.emb .run) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t rest m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hq hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walk) ⟨rgOff F hnerg hrg _ r hno, hwk⟩).2 not_false)
    hwkLt hsle).mono (by
    have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
    have h₂ : wideRank q - wideRank wkAddr ≤ wideRank (F.cell gbot) :=
      le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
    omega)


-- @@ L891-904 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk hnesrc htop hbot hwkLt hrg hrl hwkS hsrcBit
  hsle in
/-- **The kit copies a track**, the budget forgotten. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest fun u => rest (F.cell u) κ.src = PR.one)
          (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules F hR hlin hix hnerg hnerl hnewk hnesrc htop hbot hwkLt hrg hrl hwkS hsrcBit
    hsle
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))).reflTransGen


-- @@ L906-906 verbatim
end Discharge


-- @@ L908-908 verbatim
end CopyKit


-- @@ L910-926 verbatim
/-- **A track-mapping kit**: the walked track is rewritten by a bit the
*other* tracks at each register decide – the pattern writes of the program,
a target register loaded from the marks. The function ignoring the walked
slot is the discharge's frame hypothesis. -/
structure MapKit (A Q W P : Type) where
  /-- The walked track being overwritten. -/
  t : W
  /-- The register mark. -/
  rg : W
  /-- The file-top mark. -/
  rl : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The written bit, computed from the tracks. -/
  Fb : (W → A) → Prop
  /-- The kit's phases in the program. -/
  emb : TrackPh → P


-- @@ L928-928 verbatim
namespace MapKit


-- @@ L930-930 verbatim
variable {A Q W P : Type} [DecidableEq W] (κ : MapKit A Q W P) (zero one : A)


-- @@ L932-968 verbatim
/-- **The kit's rules.** -/
noncomputable def rule : TrackRule → Rule A Q W P
  | .up =>
    { guard := fun _ g => g κ.rl ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .b1 =>
    { guard := fun _ g => g κ.rl = one
      srcPh := κ.emb .up
      dstPh := κ.emb .b2
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .b2go =>
    { guard := fun _ _ => True
      srcPh := κ.emb .b2
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun _ g => g κ.rg = one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => Function.update g κ.t (bitVal zero one (κ.Fb g))
      moveRight := False }
  | .walk =>
    { guard := fun _ g => g κ.rg ≠ one ∧ g κ.wk ≠ one
      srcPh := κ.emb .run
      dstPh := κ.emb .run
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }


-- @@ L970-974 verbatim
/-- **The trip stays inside its own phases**: every rule lands in one the kit
was given, which is what a caller that must know a property of the phases the
machine can be in reads off a sub-machinery. -/
theorem dstPh_emb (ρ : TrackRule) : ∃ p, (κ.rule zero one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩


-- @@ L976-988 verbatim
/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : TrackRule) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg hg'.1
    | exact absurd hg' hg.1


-- @@ L990-999 verbatim
/-- **Exit disjointness** at the kit's pass-and-return phase. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : TrackRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → g κ.rg ≠ one →
      (κ.rule zero one ρ).srcPh = κ.emb .run → False := by
  intro ρ f g hg hwk hrg hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hg hrg
    | exact absurd hwk hg.2
    | (have hbb := hemb hph; cases hbb)


-- @@ L1001-1001 verbatim
section Discharge


-- @@ L1003-1003 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L1004-1004 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L1005-1005 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L1006-1006 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L1007-1007 verbatim
variable {PR : Prog A R P Q W K dd} {κ : MapKit A Q W P}

-- @@ L1008-1008 verbatim
variable {rEmb : TrackRule → R}

-- @@ L1009-1009 verbatim
variable (hrules : ∀ ρ : TrackRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)

-- @@ L1010-1010 verbatim
variable {I : Type} [Finite I] {ile : I → I → Prop}

-- @@ L1011-1011 verbatim
variable (F : IxFile (Univ A R P K dd) I ile)

-- @@ L1012-1012 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L1013-1013 verbatim
variable (hix : IsLinOrd ile)

-- @@ L1014-1014 verbatim
variable (hnerg : κ.t ≠ κ.rg) (hnerl : κ.rl ≠ κ.t) (hnewk : κ.wk ≠ κ.t)

-- @@ L1015-1015 verbatim
variable {gtop gbot : I} (htop : ∀ y, ile y gtop) (hbot : ∀ y, ile gbot y)

-- @@ L1016-1016 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}

-- @@ L1017-1017 verbatim
variable {wkAddr : Univ A R P K dd → Prop} (hwkLt : WMSetLt WMLe wkAddr (F.cell gbot))

-- @@ L1018-1019 verbatim
variable (hrg : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rg = bitVal PR.zero PR.one (∃ u : I, r = F.cell u))

-- @@ L1020-1021 verbatim
variable (hrl : ∀ r : Univ A R P K dd → Prop,
  rest r κ.rl = bitVal PR.zero PR.one (r = F.cell gtop))

-- @@ L1022-1023 verbatim
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = wkAddr))

-- @@ L1024-1024 verbatim
variable (hFb : ∀ g g' : W → A, (∀ s : W, s ≠ κ.t → g s = g' s) → (κ.Fb g ↔ κ.Fb g'))

-- @@ L1025-1025 verbatim
variable {fc : Q → A} {s : Univ A R P K dd → Prop}

-- @@ L1026-1026 verbatim
variable (hsle : WMSetLe WMLe s (F.cell gtop))

-- @@ L1027-1028 verbatim
variable {w : ℕ} (hgap : ∀ u u' : I, IxSucc ile u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ w)


-- @@ L1030-1052 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness, at its own
destination data. -/
private theorem has_of_rule {ρ : TrackRule} {f : Q → A} {g : W → A}
    (hg : (κ.rule PR.zero PR.one ρ).guard f g) :
    (∀ _hmr : (κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasRight (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) ∧
    (∀ _hml : ¬(κ.rule PR.zero PR.one ρ).moveRight,
      PR.HasLeft (κ.rule PR.zero PR.one ρ).srcPh f g
        (κ.rule PR.zero PR.one ρ).dstPh ((κ.rule PR.zero PR.one ρ).dstSt f g)
        ((κ.rule PR.zero PR.one ρ).wr f g)) := by
  constructor
  · intro hmr
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], by rw [hrules]; exact hmr⟩
  · intro hml
    exact ⟨rEmb ρ, by rw [hrules]; exact hg, by rw [hrules], by rw [hrules],
      by rw [hrules], by rw [hrules], fun hc => hml (by rw [hrules] at hc; exact hc)⟩


-- @@ L1054-1071 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K] [Finite I] in
include F hlin hix hnewk hbot hwkLt hwkS in
private theorem wkOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hbnd : ∃ x : I, WMSetLe WMLe (F.cell x) r) :
    PR.passTracksAt F.cell κ.t rest k r κ.wk ≠ PR.one := by
  have hlinSet := isLinOrd_wmSetLe (α := Univ A R P K dd) hlin
  obtain ⟨x, hx⟩ := hbnd
  have hgx : WMSetLe WMLe (F.cell gbot) (F.cell x) := by
    rcases eq_or_ne gbot x with rfl | hne
    · exact hlinSet.1 _
    · exact ((wmSetLt_iff _ _).mp ((F.lt_iff hix gbot x).mpr
        ⟨hbot x, fun hc => hne (hix.2.2.1 gbot x (hbot x) hc)⟩)).1
  have hne : r ≠ wkAddr := by
    rintro rfl
    exact ((wmSetLt_iff _ _).mp hwkLt).2
      (hlinSet.2.2.1 _ _ ((wmSetLt_iff _ _).mp hwkLt).1 (hlinSet.2.1 _ _ _ hgx hx))
  rw [Prog.passTracks_of_ne hnewk, hwkS, bitVal_neg hne]
  exact PR.zero_ne_one


-- @@ L1073-1081 verbatim
omit [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Finite A] [Finite R] [Finite P] [Finite K] [Finite I] in
include F hnerg hrg in
private theorem rgOff (k : I → Prop) (r : Univ A R P K dd → Prop)
    (hno : ∀ x : I, r ≠ F.cell x) :
    PR.passTracksAt F.cell κ.t rest k r κ.rg ≠ PR.one := by
  rw [Prog.passTracks_of_ne (Ne.symm hnerg), hrg,
    bitVal_neg fun hc => hc.elim fun x hx => hno x hx]
  exact PR.zero_ne_one


-- @@ L1083-1120 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hFb hsle hgap in
/-- **The kit rewrites its track by the function**: from the scan phase
anywhere, up to the file top, one pass writing the computed bit at every
register, and back to the marker. -/
theorem reachesIn :
    (wideData (Univ A R P K dd)).ReachesIn
      (wideRank (F.cell gtop) + 2 + ((ixRank ile gtop - ixRank ile gbot) * w + 1) +
        wideRank (F.cell gbot))
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest
          fun u => κ.Fb (PR.passTracksAt F.cell κ.t rest m (F.cell u))) (PR.syElt PR.blank)⟩ := by
  obtain ⟨q, hq, hpass⟩ := Prog.reachesIn_fileMapTrack F hR hlin hix (t := κ.t) (rg := κ.rg)
    hnerg (rest := rest) hrg (Fb := κ.Fb) hFb (m := m) (p := κ.emb .run) (f := fc)
    (fun _g hg1 => (has_of_rule hrules (ρ := .put) hg1).2 not_false)
    (fun k r hbnd hno =>
      (has_of_rule hrules (ρ := .walk)
        ⟨rgOff F hnerg hrg k r hno, wkOff F hlin hix hnewk hbot hwkLt hwkS k r hbnd⟩).2
        not_false)
    (w := w) hgap (top := gtop) (bot := gbot) htop hbot
  refine (Prog.reachesIn_fileRoundTrip F hR hlin hix hnerl hnewk hbot (rest := rest)
    (m := m) (m₂ := fun u => κ.Fb (PR.passTracksAt F.cell κ.t rest m (F.cell u)))
    (wkAddr := wkAddr) hrl hwkS (p₁ := κ.emb .up)
    (p₂b := κ.emb .b2) (pIn := κ.emb .run) (pOut := κ.emb .run) (fc := fc)
    (fun _g hg => (has_of_rule hrules (ρ := .up) hg).1 trivial)
    ((has_of_rule hrules (ρ := .b1)
      (show PR.passTracksAt F.cell κ.t rest m (F.cell gtop) κ.rl = PR.one by
        rw [Prog.passTracks_of_ne hnerl, hrl]; exact bitVal_pos rfl)).2 not_false)
    (fun _g => (has_of_rule hrules (ρ := .b2go) trivial).1 trivial)
    hq hpass
    (fun r hno hwk =>
      (has_of_rule hrules (ρ := .walk) ⟨rgOff F hnerg hrg _ r hno, hwk⟩).2 not_false)
    hwkLt hsle).mono (by
    have h₁ : wideRank (F.cell gtop) - wideRank s ≤ wideRank (F.cell gtop) := Nat.sub_le _ _
    have h₂ : wideRank q - wideRank wkAddr ≤ wideRank (F.cell gbot) :=
      le_trans (Nat.sub_le _ _) (wideRank_mono hlin (wmSetLe_of_wmIncr hq))
    omega)


-- @@ L1122-1133 verbatim
include hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hFb hsle in
/-- **The kit rewrites a track**, the budget forgotten. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .up) fc), Sum.inl s,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .run) fc), Sum.inl wkAddr,
        wideTape (PR.trackTapeAt F.cell κ.t rest
          fun u => κ.Fb (PR.passTracksAt F.cell κ.t rest m (F.cell u))) (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules F hR hlin hix hnerg hnerl hnewk htop hbot hwkLt hrg hrl hwkS hFb hsle
    (w := Nat.card {q : WPoint (Univ A R P K dd) // (wideData (Univ A R P K dd)).Posn q})
    (fun _ _ _ => le_trans (Nat.sub_le _ _) (Nat.le_of_lt (wideRank_lt_card _)))).reflTransGen


-- @@ L1135-1135 verbatim
end Discharge


-- @@ L1137-1137 verbatim
end MapKit


-- @@ L1139-1139 verbatim
end Draw


-- @@ L1141-1141 verbatim
end DescriptiveComplexity
