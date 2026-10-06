/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRead


-- @@ L8-37 verbatim
/-!
# Composite kits: how the program instantiates its subroutines

The composites of the layer take their phases and rule families as parameters
(“no continuation labels”: a program's phase set is its list of call sites).
The program therefore assembles as a sum of **kits**, one per composite shape:

* a *phase shape* – a small inductive, one constructor per phase the composite
  visits (`DescriptiveComplexity.Draw.ReadPh`);
* a *rule shape* – one constructor per rule family, each with its concrete
  guard (`DescriptiveComplexity.Draw.ReadRule`);
* the *rules function* – the shape's `DescriptiveComplexity.Draw.Rule`s, at a
  phase embedding and the kit's slots
  (`DescriptiveComplexity.Draw.ReadKit.rule`);
* a *discharge* – any program whose rule set contains the kit's rules
  satisfies the composite's rule hypotheses, so the composite's run theorem
  holds for it (`DescriptiveComplexity.Draw.ReadKit.reaches_pos`/`_neg`);
* an *in-shape separation* lemma – two of the kit's rules firing in the same
  phase on the same data are the same rule
  (`DescriptiveComplexity.Draw.ReadKit.sep`).

Global determinism then reduces to: each kit separates in-shape, the phase
embeddings are injective, and distinct kits use disjoint phases – the source
phase of a rule names its kit, so `DescriptiveComplexity.Draw.Prog.sep_of`'s
hypothesis never crosses kits.

This file builds the smallest kit with full content – the named-bit read of
`DescriptiveComplexity.Problems.Wide.DrawRead` – as the template the others
follow.
-/


-- @@ L39-39 verbatim
namespace DescriptiveComplexity


-- @@ L41-41 verbatim
namespace Draw


-- @@ L43-43 verbatim
open FirstOrder


-- @@ L45-45 verbatim
open Language Structure


-- @@ L47-47 verbatim
/-! ### Summing kits: separation of a program assembled from sites -/


-- @@ L49-70 verbatim
/-- **Separation of a program assembled from kits**: when the rule names are a
sigma of per-site shapes, every rule's source phase is owned by its site, and
each site separates in-shape, the whole program separates. This is the form
`DescriptiveComplexity.Draw.Prog.sep_of` receives from an assembly: the
cross-site case is settled by ownership, the in-site case by the kits'
`sep` lemmas – which is why a kit's exit rules, fired from another kit's end
phases, must be grouped under the site owning those *phases*, not the site
they serve. -/
theorem sep_sigma {A Q W P S : Type} {Sh : S → Type}
    (rules : (Σ i : S, Sh i) → Rule A Q W P) (owner : P → S)
    (howner : ∀ (i : S) (ρ : Sh i), owner (rules ⟨i, ρ⟩).srcPh = i)
    (hsep : ∀ (i : S) (ρ ρ' : Sh i) (f : Q → A) (g : W → A),
      (rules ⟨i, ρ⟩).guard f g → (rules ⟨i, ρ'⟩).guard f g →
      (rules ⟨i, ρ⟩).srcPh = (rules ⟨i, ρ'⟩).srcPh → ρ = ρ') :
    ∀ (r r' : Σ i : S, Sh i) (f : Q → A) (g : W → A),
      (rules r).guard f g → (rules r').guard f g →
      (rules r).srcPh = (rules r').srcPh → r = r' := by
  rintro ⟨i, ρ⟩ ⟨j, ρ'⟩ f g hg hg' hph
  have hij : i = j := by
    rw [← howner i ρ, ← howner j ρ', hph]
  subst hij
  rw [hsep i ρ ρ' f g hg hg' hph]


-- @@ L72-72 verbatim
/-! ### The read trip's shapes -/


-- @@ L74-85 verbatim
/-- **The phases of a read trip**: at the marker, scanning up, and the two
verdict returns. -/
inductive ReadPh : Type
  /-- At the working-cell marker, about to leave. -/
  | start : ReadPh
  /-- Scanning up to the named cell. -/
  | up : ReadPh
  /-- The bit was set: returning. -/
  | ry : ReadPh
  /-- The bit was clear: returning. -/
  | rn : ReadPh
  deriving DecidableEq


-- @@ L87-91 verbatim
instance : Finite ReadPh :=
  Finite.of_injective
    (fun p => match p with
      | .start => (0 : Fin 4) | .up => 1 | .ry => 2 | .rn => 3)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L93-110 verbatim
/-- **The rule families of a read trip**, one constructor each. -/
inductive ReadRule : Type
  /-- Leave the marker rightwards. -/
  | turn : ReadRule
  /-- Scan right while the name does not match. -/
  | up : ReadRule
  /-- At the named cell with the bit set: branch positive, step left. -/
  | rd1 : ReadRule
  /-- At the named cell with the bit clear: branch negative, step left. -/
  | rd0 : ReadRule
  /-- Return leftwards in the positive phase. -/
  | backY : ReadRule
  /-- Return leftwards in the negative phase. -/
  | backN : ReadRule
  /-- Walk left back to the marker before leaving it: what lets a dispatch
  enter the trip by stepping right off the marker. -/
  | stayS : ReadRule
  deriving DecidableEq


-- @@ L112-117 verbatim
instance : Finite ReadRule :=
  Finite.of_injective
    (fun p => match p with
      | .turn => (0 : Fin 7) | .up => 1 | .rd1 => 2 | .rd0 => 3 | .backY => 4 | .backN => 5
      | .stayS => 6)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L119-119 verbatim
/-! ### The kit -/


-- @@ L121-131 verbatim
/-- **A read-trip kit**: the two slots it reads, the name guard, and where its
phases sit in the program. -/
structure ReadKit (A Q W P : Type) where
  /-- The walked track being read. -/
  t : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The name guard: this cell is the one the control names. -/
  Match : (Q → A) → (W → A) → Prop
  /-- The kit's phases in the program. -/
  emb : ReadPh → P


-- @@ L133-133 verbatim
namespace ReadKit


-- @@ L135-135 verbatim
variable {A Q W P : Type} (κ : ReadKit A Q W P) (one : A)


-- @@ L137-188 verbatim
/-- **The kit's rules.** Every attribute is a function of the constructor, and
every guard is decided by the slots the shape reads. -/
def rule : ReadRule → Rule A Q W P
  | .turn =>
    { guard := fun _ g => g κ.wk = one
      srcPh := κ.emb .start
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .up =>
    { guard := fun f g => ¬κ.Match f g
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .rd1 =>
    { guard := fun f g => κ.Match f g ∧ g κ.t = one
      srcPh := κ.emb .up
      dstPh := κ.emb .ry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .rd0 =>
    { guard := fun f g => κ.Match f g ∧ g κ.t ≠ one
      srcPh := κ.emb .up
      dstPh := κ.emb .rn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .backY =>
    { guard := fun _ g => g κ.wk ≠ one
      srcPh := κ.emb .ry
      dstPh := κ.emb .ry
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .backN =>
    { guard := fun _ g => g κ.wk ≠ one
      srcPh := κ.emb .rn
      dstPh := κ.emb .rn
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stayS =>
    { guard := fun _ g => g κ.wk ≠ one
      srcPh := κ.emb .start
      dstPh := κ.emb .start
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }


-- @@ L190-206 verbatim
/-- **In-shape separation**: two of the kit's rules firing in the same phase on
the same data are the same rule. The phase splits the families into four
groups, and within a group the guards are mutually exclusive. -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : ReadRule) (f : Q → A) (g : W → A),
      (κ.rule one ρ).guard f g → (κ.rule one ρ').guard f g →
      (κ.rule one ρ).srcPh = (κ.rule one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'
    | exact absurd hg'.1 hg
    | exact absurd hg.1 hg'
    | exact absurd hg'.2 hg.2
    | exact absurd hg.2 hg'.2


-- @@ L208-214 verbatim
/-- **A trip stays inside its own phases**: every rule of the kit lands in one
of the four the kit was given, so a caller that knows a property of those
knows it of every phase the trip can be in. This is what a determinism-after-
the-guess argument needs of a sub-machinery
(`DescriptiveComplexity.Draw.Data.nexProg_uniqueFrom`). -/
theorem dstPh_emb (ρ : ReadRule) : ∃ p : ReadPh, (κ.rule one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩


-- @@ L216-226 verbatim
/-- **Exit disjointness** at the kit's two verdict phases: no kit rule fires
there on a symbol with the marker set. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : ReadRule) (f : Q → A) (g : W → A), (κ.rule one ρ).guard f g →
      g κ.wk = one →
      ((κ.rule one ρ).srcPh = κ.emb .ry ∨ (κ.rule one ρ).srcPh = κ.emb .rn) →
      False := by
  intro ρ f g hg hwk hph
  cases ρ <;> simp only [rule] at hg hph <;> rcases hph with hph | hph <;> first
    | exact absurd hwk hg
    | (have hbb := hemb hph; cases hbb)


-- @@ L228-228 verbatim
/-! ### The discharge -/


-- @@ L230-230 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L231-231 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L232-232 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L233-233 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L234-234 verbatim
variable {PR : Prog A R P Q W K dd} {κ : ReadKit A Q W P}

-- @@ L235-235 verbatim
variable {rEmb : ReadRule → R}

-- @@ L236-236 verbatim
variable (hrules : ∀ ρ : ReadRule, PR.rules (rEmb ρ) = κ.rule PR.one ρ)


-- @@ L238-261 verbatim
omit [DecidableEq W] [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)]
  [Finite A] [Finite R] [Finite P] [Finite K] in
include hrules in
/-- A kit rule with a true guard is a `HasRight`/`HasLeft` witness. -/
private theorem has_of_rule {ρ : ReadRule} {f : Q → A} {g : W → A}
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


-- @@ L263-263 verbatim
variable {I : Type} {ile : I → I → Prop}

-- @@ L264-264 verbatim
variable (F : IxFile (Univ A R P K dd) I ile)

-- @@ L265-265 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L266-266 verbatim
variable (hix : IsLinOrd ile)

-- @@ L267-267 verbatim
variable (hnewk : κ.wk ≠ κ.t)

-- @@ L268-268 verbatim
variable {gbot : I} (hbot : ∀ y, ile gbot y)

-- @@ L269-269 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}

-- @@ L270-270 verbatim
variable {v : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (F.cell gbot))

-- @@ L271-272 verbatim
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = v))

-- @@ L273-273 verbatim
variable {fc : Q → A} {x₀ : I}

-- @@ L274-274 verbatim
variable (hname : κ.Match fc (PR.passTracksAt F.cell κ.t rest m (F.cell x₀)))

-- @@ L275-276 verbatim
variable (huniq : ∀ r : Univ A R P K dd → Prop,
  κ.Match fc (PR.passTracksAt F.cell κ.t rest m r) → r = F.cell x₀)


-- @@ L278-293 verbatim
include hrules hR hlin hix hnewk hbot hv hwkS hname huniq in
/-- **The kit reads a set bit**: the composite's run theorem, with every rule
hypothesis discharged from the kit's rules. -/
theorem reachesIn_pos (hm : m x₀) :
    (wideData (Univ A R P K dd)).ReachesIn (2 * (wideRank (F.cell x₀) - wideRank v) + 2)
      ⟨Sum.inr (PR.stElt (κ.emb .start) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ry) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ := by
  refine Prog.reachesIn_readBit_pos (F := F) (NameG := κ.Match fc) (pUp := κ.emb .up)
    hR hlin hix hnewk hbot hv hwkS hname huniq
    (fun g hg => ?_) (fun g hg => ?_) (fun g hg hb => ?_) (fun g hg => ?_) hm
  · exact ((has_of_rule hrules (ρ := .turn) hg rfl rfl).1 trivial)
  · exact ((has_of_rule hrules (ρ := .up) hg rfl rfl).1 trivial)
  · exact ((has_of_rule hrules (ρ := .rd1) ⟨hg, hb⟩ rfl rfl).2 not_false)
  · exact ((has_of_rule hrules (ρ := .backY) hg rfl rfl).2 not_false)


-- @@ L295-303 verbatim
include hrules hR hlin hix hnewk hbot hv hwkS hname huniq in
/-- **The kit reads a set bit**, the budget forgotten. -/
theorem reaches_pos (hm : m x₀) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .start) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .ry) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_pos hrules F hR hlin hix hnewk hbot hv hwkS hname huniq hm).reflTransGen


-- @@ L305-319 verbatim
include hrules hR hlin hix hnewk hbot hv hwkS hname huniq in
/-- **The kit reads a clear bit.** -/
theorem reachesIn_neg (hm : ¬m x₀) :
    (wideData (Univ A R P K dd)).ReachesIn (2 * (wideRank (F.cell x₀) - wideRank v) + 2)
      ⟨Sum.inr (PR.stElt (κ.emb .start) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .rn) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ := by
  refine Prog.reachesIn_readBit_neg (F := F) (NameG := κ.Match fc) (pUp := κ.emb .up)
    hR hlin hix hnewk hbot hv hwkS hname huniq
    (fun g hg => ?_) (fun g hg => ?_) (fun g hg hb => ?_) (fun g hg => ?_) hm
  · exact ((has_of_rule hrules (ρ := .turn) hg rfl rfl).1 trivial)
  · exact ((has_of_rule hrules (ρ := .up) hg rfl rfl).1 trivial)
  · exact ((has_of_rule hrules (ρ := .rd0) ⟨hg, hb⟩ rfl rfl).2 not_false)
  · exact ((has_of_rule hrules (ρ := .backN) hg rfl rfl).2 not_false)


-- @@ L321-329 verbatim
include hrules hR hlin hix hnewk hbot hv hwkS hname huniq in
/-- **The kit reads a clear bit**, the budget forgotten. -/
theorem reaches_neg (hm : ¬m x₀) :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .start) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .rn) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩ :=
  (reachesIn_neg hrules F hR hlin hix hnewk hbot hv hwkS hname huniq hm).reflTransGen


-- @@ L331-331 verbatim
end ReadKit


-- @@ L333-337 verbatim
/-! ### The write trip's shapes

The same trip writing the digit: the kit carries the written bit as a
function of the control payload, so one shape serves constant writes and
writes of a previously computed bit alike. -/


-- @@ L339-347 verbatim
/-- **The phases of a write trip.** -/
inductive WritePh : Type
  /-- At the working-cell marker, about to leave. -/
  | start : WritePh
  /-- Scanning up to the named cell. -/
  | up : WritePh
  /-- Written: returning. -/
  | back : WritePh
  deriving DecidableEq


-- @@ L349-352 verbatim
instance : Finite WritePh :=
  Finite.of_injective
    (fun p => match p with | .start => (0 : Fin 3) | .up => 1 | .back => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L354-366 verbatim
/-- **The rule families of a write trip.** -/
inductive WriteRule : Type
  /-- Leave the marker rightwards. -/
  | turn : WriteRule
  /-- Scan right while the name does not match. -/
  | up : WriteRule
  /-- At the named cell: write the bit, step left. -/
  | put : WriteRule
  /-- Return leftwards. -/
  | back : WriteRule
  /-- Walk left back to the marker before leaving it. -/
  | stayS : WriteRule
  deriving DecidableEq


-- @@ L368-372 verbatim
instance : Finite WriteRule :=
  Finite.of_injective
    (fun p => match p with
      | .turn => (0 : Fin 5) | .up => 1 | .put => 2 | .back => 3 | .stayS => 4)
    (by intro a b h; cases a <;> cases b <;> simp_all)


-- @@ L374-386 verbatim
/-- **A write-trip kit**: the slots, the name guard, the written bit as a
function of the payload, and the phases. -/
structure WriteKit (A Q W P : Type) where
  /-- The walked track being written. -/
  t : W
  /-- The working-cell marker slot. -/
  wk : W
  /-- The name guard. -/
  Match : (Q → A) → (W → A) → Prop
  /-- The written bit, as a function of the payload. -/
  bVal : (Q → A) → Prop
  /-- The kit's phases in the program. -/
  emb : WritePh → P


-- @@ L388-388 verbatim
namespace WriteKit


-- @@ L390-390 verbatim
variable {A Q W P : Type} [DecidableEq W] (κ : WriteKit A Q W P) (zero one : A)


-- @@ L392-428 verbatim
/-- **The kit's rules.** -/
noncomputable def rule : WriteRule → Rule A Q W P
  | .turn =>
    { guard := fun _ g => g κ.wk = one
      srcPh := κ.emb .start
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .up =>
    { guard := fun f g => ¬κ.Match f g
      srcPh := κ.emb .up
      dstPh := κ.emb .up
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := True }
  | .put =>
    { guard := fun f g => κ.Match f g
      srcPh := κ.emb .up
      dstPh := κ.emb .back
      dstSt := fun f _ => f
      wr := fun f g => Function.update g κ.t (bitVal zero one (κ.bVal f))
      moveRight := False }
  | .back =>
    { guard := fun _ g => g κ.wk ≠ one
      srcPh := κ.emb .back
      dstPh := κ.emb .back
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }
  | .stayS =>
    { guard := fun _ g => g κ.wk ≠ one
      srcPh := κ.emb .start
      dstPh := κ.emb .start
      dstSt := fun f _ => f
      wr := fun _ g => g
      moveRight := False }


-- @@ L430-436 verbatim
/-- **A write trip stays inside its own phases**: every rule of the kit lands
in one of the phases the kit was given, which is what a
determinism-after-the-guess argument needs of a sub-machinery
(`DescriptiveComplexity.Draw.Data.nexProg_uniqueFrom`). -/
theorem dstPh_emb (ρ : WriteRule) :
    ∃ p : WritePh, (κ.rule zero one ρ).dstPh = κ.emb p := by
  cases ρ <;> exact ⟨_, rfl⟩


-- @@ L438-448 verbatim
/-- **In-shape separation.** -/
theorem sep (hemb : Function.Injective κ.emb) :
    ∀ (ρ ρ' : WriteRule) (f : Q → A) (g : W → A),
      (κ.rule zero one ρ).guard f g → (κ.rule zero one ρ').guard f g →
      (κ.rule zero one ρ).srcPh = (κ.rule zero one ρ').srcPh → ρ = ρ' := by
  intro ρ ρ' f g hg hg' hph
  cases ρ <;> cases ρ' <;> simp only [rule] at hg hg' hph <;> first
    | rfl
    | exact absurd (hemb hph) (fun h => nomatch h)
    | exact absurd hg' hg
    | exact absurd hg hg'


-- @@ L450-458 verbatim
/-- **Exit disjointness** at the kit's return phase: no kit rule fires there
on a symbol with the marker set. -/
theorem exit_disjoint (hemb : Function.Injective κ.emb) :
    ∀ (ρ : WriteRule) (f : Q → A) (g : W → A), (κ.rule zero one ρ).guard f g →
      g κ.wk = one → (κ.rule zero one ρ).srcPh = κ.emb .back → False := by
  intro ρ f g hg hwk hph
  cases ρ <;> simp only [rule] at hg hph <;> first
    | exact absurd hwk hg
    | (have hbb := hemb hph; cases hbb)


-- @@ L460-460 verbatim
section Discharge


-- @@ L462-462 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L463-463 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L464-464 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L465-465 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L466-466 verbatim
variable {PR : Prog A R P Q W K dd} {κ : WriteKit A Q W P}

-- @@ L467-467 verbatim
variable {rEmb : WriteRule → R}

-- @@ L468-468 verbatim
variable (hrules : ∀ ρ : WriteRule, PR.rules (rEmb ρ) = κ.rule PR.zero PR.one ρ)

-- @@ L469-469 verbatim
variable {I : Type} {ile : I → I → Prop}

-- @@ L470-470 verbatim
variable (F : IxFile (Univ A R P K dd) I ile)

-- @@ L471-471 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L472-472 verbatim
variable (hix : IsLinOrd ile)

-- @@ L473-473 verbatim
variable (hnewk : κ.wk ≠ κ.t)

-- @@ L474-474 verbatim
variable {gbot : I} (hbot : ∀ y, ile gbot y)

-- @@ L475-475 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A} {m : I → Prop}

-- @@ L476-476 verbatim
variable {v : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (F.cell gbot))

-- @@ L477-478 verbatim
variable (hwkS : ∀ r : Univ A R P K dd → Prop,
  rest r κ.wk = bitVal PR.zero PR.one (r = v))

-- @@ L479-479 verbatim
variable {fc : Q → A} {x₀ : I}

-- @@ L480-480 verbatim
variable (hname : κ.Match fc (PR.passTracksAt F.cell κ.t rest m (F.cell x₀)))

-- @@ L481-482 verbatim
variable (huniq : ∀ r : Univ A R P K dd → Prop,
  κ.Match fc (PR.passTracksAt F.cell κ.t rest m r) → r = F.cell x₀)


-- @@ L484-505 verbatim
include hrules hR hlin hix hnewk hbot hv hwkS hname huniq in
/-- **The kit writes its bit at the named cell** and returns to the marker. -/
theorem reachesIn :
    (wideData (Univ A R P K dd)).ReachesIn (2 * (wideRank (F.cell x₀) - wideRank v) + 2)
      ⟨Sum.inr (PR.stElt (κ.emb .start) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .back) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest
          fun y => (y = x₀ ∧ κ.bVal fc) ∨ (y ≠ x₀ ∧ m y)) (PR.syElt PR.blank)⟩ := by
  refine Prog.reachesIn_writeBit (F := F) (NameG := κ.Match fc) (pUp := κ.emb .up)
    hR hlin hix hnewk hbot hv hwkS hname huniq
    (fun g hg => ?_) (fun g hg => ?_) (b := κ.bVal fc) ?_ (fun g hg => ?_)
  · exact ⟨rEmb .turn, by rw [hrules]; exact hg, by rw [hrules]; rfl, by rw [hrules]; rfl,
      by rw [hrules]; rfl, by rw [hrules]; rfl, by rw [hrules]; trivial⟩
  · exact ⟨rEmb .up, by rw [hrules]; exact hg, by rw [hrules]; rfl, by rw [hrules]; rfl,
      by rw [hrules]; rfl, by rw [hrules]; rfl, by rw [hrules]; trivial⟩
  · exact ⟨rEmb .put, by rw [hrules]; exact hname, by rw [hrules]; rfl, by rw [hrules]; rfl,
      by rw [hrules]; rfl, by rw [hrules]; rfl,
      fun hc => by rw [hrules] at hc; exact hc⟩
  · exact ⟨rEmb .back, by rw [hrules]; exact hg, by rw [hrules]; rfl, by rw [hrules]; rfl,
      by rw [hrules]; rfl, by rw [hrules]; rfl,
      fun hc => by rw [hrules] at hc; exact hc⟩


-- @@ L507-516 verbatim
include hrules hR hlin hix hnewk hbot hv hwkS hname huniq in
/-- **The kit writes a named bit**, the budget forgotten. -/
theorem reaches :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (κ.emb .start) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest m) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (κ.emb .back) fc), Sum.inl v,
        wideTape (PR.trackTapeAt F.cell κ.t rest
          fun y => (y = x₀ ∧ κ.bVal fc) ∨ (y ≠ x₀ ∧ m y)) (PR.syElt PR.blank)⟩ :=
  (reachesIn hrules F hR hlin hix hnewk hbot hv hwkS hname huniq ).reflTransGen


-- @@ L518-518 verbatim
end Discharge


-- @@ L520-520 verbatim
end WriteKit


-- @@ L522-522 verbatim
end Draw


-- @@ L524-524 verbatim
end DescriptiveComplexity
