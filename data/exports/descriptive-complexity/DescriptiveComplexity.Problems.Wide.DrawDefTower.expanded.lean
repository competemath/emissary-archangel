/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawDefKit
import DescriptiveComplexity.Problems.Wide.DrawTuple
import DescriptiveComplexity.Problems.Wide.DrawTagged
import DescriptiveComplexity.Problems.Wide.DrawSeq


-- @@ L11-26 verbatim
/-!
# The combinators carry definability up the tower

`DescriptiveComplexity.Problems.Wide.DrawDefKit` discharges the leaves; this file
carries `DescriptiveComplexity.Draw.URuleDefinable` through the *combinators* the
EXPSPACE program is assembled by – the chain, the sequencer, the element loop,
the tag-branched machinery and the tuple loop.

Each combinator contributes only checkpoints, and a checkpoint's rule has the
same three shapes everywhere: a walk back to the marker (`stay`), and one or two
dispatches, whose guards are the standard exit guard conjoined with a question
the caller supplies and whose destination pointers are the caller's control
updates. So each proof is: the leaves by
`DescriptiveComplexity.Problems.Wide.DrawDefKit`, the checkpoints by the atoms,
and nothing else.
-/


-- @@ L28-28 verbatim
namespace DescriptiveComplexity


-- @@ L30-30 verbatim
namespace Draw


-- @@ L32-32 verbatim
open FirstOrder


-- @@ L34-34 verbatim
open Language Structure


-- @@ L36-36 verbatim
variable {L : Language.{0, 0}} {Q W P : Type} [Fintype Q] [Fintype W]


-- @@ L38-38 verbatim
/-! ### A rule may be transported along an equality of families -/


-- @@ L40-48 verbatim
theorem URuleDefinable.congr {rl rl' : ∀ e : Env L, Rule e.α Q W P}
    (h : URuleDefinable rl) (he : ∀ e : Env L, rl' e = rl e) :
    URuleDefinable rl' where
  srcPh := h.srcPh.imp fun _ hp e => by rw [he]; exact hp e
  dstPh := h.dstPh.imp fun _ hp e => by rw [he]; exact hp e
  right := h.right.imp fun _ hp e => by rw [he]; exact hp e
  guard := h.guard.congr fun e f g => by rw [he]
  dst := h.dst.congr fun e f g q => by rw [he]
  wr := h.wr.congr fun e f g s => by rw [he]


-- @@ L50-50 verbatim
/-! ### A rule without its source phase -/


-- @@ L52-64 verbatim
/-- **A dispatch descriptor is definable**: the same three obligations, its
source phase being the checkpoint's. -/
structure UPreDefinable (pr : ∀ e : Env L, PreRule e.α Q W P) : Prop where
  /-- The phase it moves to is the same at every instance. -/
  dstPh : ∃ p : P, ∀ e : Env L, (pr e).dstPh = p
  /-- And so is its direction. -/
  right : ∃ b : Bool, ∀ e : Env L, ((pr e).moveRight ↔ b = true)
  /-- Its guard reads its data only through the equality pattern. -/
  guard : UGDefinable fun e => (pr e).guard
  /-- The pointer it leaves is definable slot by slot. -/
  dst : UStDefinable fun e => (pr e).dstSt
  /-- And so are the tracks it writes. -/
  wr : UTrDefinable fun e => (pr e).wr


-- @@ L66-70 verbatim
/-- **A descriptor at a source phase is a definable rule.** -/
theorem UPreDefinable.toRule {pr : ∀ e : Env L, PreRule e.α Q W P}
    (h : UPreDefinable pr) (p : P) :
    URuleDefinable fun e => (pr e).toRule p :=
  ⟨⟨p, fun _ => rfl⟩, h.dstPh, h.right, h.guard, h.dst, h.wr⟩


-- @@ L72-90 verbatim
/-- **The dispatch shape of every checkpoint**: the standard exit guard,
conjoined with a question the caller supplies, a control update and the tracks
riding along. -/
theorem uPreDefinable_dsp {wk rg : W} {p : P} {b : Bool}
    {N : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {F : ∀ e : Env L, (Q → e.α) → (W → e.α) → Q → e.α}
    (hN : UGDefinable N) (hF : UStDefinable F) :
    UPreDefinable fun e =>
      { guard := fun f g => (g wk = e.one ∧ g rg ≠ e.one) ∧ N e f g
        dstPh := p
        dstSt := F e
        wr := fun _ g => g
        moveRight := b = true : PreRule e.α Q W P } where
  dstPh := ⟨p, fun _ => rfl⟩
  right := ⟨b, fun _ => Iff.rfl⟩
  guard := (((uGDefinable_trkOne (L := L) (Q := Q) wk).and
    (uGDefinable_trkOne (L := L) (Q := Q) rg).not).and hN)
  dst := hF
  wr := (uTrDefinable_id (L := L) (Q := Q) (W := W)).congr fun _ _ _ _ => rfl


-- @@ L92-92 verbatim
/-! ### The chain -/


-- @@ L94-94 verbatim
section Chain


-- @@ L96-96 verbatim
variable {PS SS : Type} {n : ℕ} {ShS : SS → Type}


-- @@ L98-114 verbatim
/-- **A chain's rules are definable**: its stages' are the parameter, and each
checkpoint contributes the walk back and its two descriptors. -/
theorem uRulesDefinable_chainRule {wk : W} {emb : ChainPh n PS → P}
    {ruleS : ∀ e : Env L, ∀ s : SS, ShS s → Rule e.α Q W P}
    {dsp : ∀ e : Env L, Fin n → Bool → PreRule e.α Q W P}
    (hS : URulesDefinable ruleS)
    (hdsp : ∀ (k : Fin n) (b : Bool), UPreDefinable fun e => dsp e k b) :
    URulesDefinable (Q := Q) fun e => chainRule e.one wk emb (ruleS e) (dsp e) := by
  rintro (k | s) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩
        (uGDefinable_trkOne (L := L) (Q := Q) wk).not (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA => exact (hdsp k false).toRule _
    | .dspB => exact (hdsp k true).toRule _
  · exact hS s ρ


-- @@ L116-116 verbatim
end Chain


-- @@ L118-118 verbatim
/-! ### The sequencer -/


-- @@ L120-120 verbatim
section Seq


-- @@ L122-122 verbatim
variable {n : ℕ} {PA SA : Fin n → Type} {ShA : ∀ a : Fin n, SA a → Type}


-- @@ L124-159 verbatim
/-- **A sequencer's rules are definable**: its stages' are the parameter, its
dispatch enters the next stage with the caller's control update or leaves after
the last, and the second descriptor is dead. -/
theorem uRulesDefinable_seqRule {wk rg : W} {emb : SeqPh n PA → P}
    {ruleA : ∀ e : Env L, ∀ (a : Fin n) (s : SA a), ShA a s → Rule e.α Q W P}
    {entry : ∀ a : Fin n, PA a}
    {enterSt : ∀ e : Env L, Fin n → (Q → e.α) → (W → e.α) → Q → e.α}
    {exitPh : P}
    (hA : ∀ (a : Fin n) (s : SA a) (ρ : ShA a s),
      URuleDefinable fun e => ruleA e a s ρ)
    (hen : ∀ a : Fin n, UStDefinable fun e => enterSt e a) :
    URulesDefinable (Q := Q) fun e =>
      seqRule e.one wk rg emb (ruleA e) entry (enterSt e) exitPh := by
  rintro (k | ⟨a, s⟩) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩
        (uGDefinable_trkOne (L := L) (Q := Q) wk).not (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      have hg : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g =>
          g wk = e.one ∧ g rg ≠ e.one :=
        (uGDefinable_trkOne (L := L) (Q := Q) wk).and
          (uGDefinable_trkOne (L := L) (Q := Q) rg).not
      by_cases hk : (k : ℕ) < n
      · simp only [seqRule, dite_eq_left hk]
        exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ hg (hen ⟨(k : ℕ), hk⟩) fun _ _ _ => rfl
      · simp only [seqRule, dite_eq_right hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ hg (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · exact hA a s ρ


-- @@ L161-161 verbatim
end Seq


-- @@ L163-163 verbatim
/-! ### The element loop -/


-- @@ L165-165 verbatim
section Elem


-- @@ L167-167 verbatim
variable {nr : ℕ}


-- @@ L169-218 verbatim
/-- **An element loop's rules are definable**: the read trips by
`DescriptiveComplexity.Draw.ReadKit.uRuleDefinable`, and the three checkpoints –
the entry, each read's verdict exit and the fold – by the dispatch shape. -/
theorem uRulesDefinable_elemRule {wk rg : W} {emb : ElemPh nr → P}
    {rdTrack : Fin nr → W}
    {MatchOf : Fin nr → ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {setFlag : ∀ e : Env L, Fin nr → Bool → (Q → e.α) → (W → e.α) → Q → e.α}
    {initEl advEl exitSt : ∀ e : Env L, (Q → e.α) → (W → e.α) → Q → e.α}
    {IsMaxEl : ∀ e : Env L, (Q → e.α) → Prop} {exitPh : P}
    (hM : ∀ j, UGDefinable (MatchOf j))
    (hset : ∀ (j : Fin nr) (b : Bool), UStDefinable fun e => setFlag e j b)
    (hinit : UStDefinable initEl) (hadv : UStDefinable advEl)
    (hexit : UStDefinable exitSt)
    (hmax : UGDefinable fun e f (_ : W → e.α) => IsMaxEl e f) :
    URulesDefinable fun e =>
      elemRule e.one wk rg emb rdTrack (fun j => MatchOf j e) (setFlag e)
        (initEl e) (advEl e) (exitSt e) (IsMaxEl e) exitPh := by
  have hstay : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g => ¬(g wk = e.one) :=
    (uGDefinable_trkOne (L := L) (Q := Q) wk).not
  have hg : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g =>
      g wk = e.one ∧ g rg ≠ e.one :=
    (uGDefinable_trkOne (L := L) (Q := Q) wk).and
      (uGDefinable_trkOne (L := L) (Q := Q) rg).not
  rintro (_ | j | _) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hg hinit fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_false (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact ReadKit.uRuleDefinable (hM j) σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hg (hset j b) fun _ _ _ => rfl
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dspA =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (hg.and hmax.not) hadv fun _ _ _ => rfl
    | .dspB =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (hg.and hmax) hexit fun _ _ _ => rfl


-- @@ L220-220 verbatim
end Elem


-- @@ L222-222 verbatim
/-! ### The tag-branched machinery -/


-- @@ L224-224 verbatim
section Tag


-- @@ L226-226 verbatim
variable {T : Type} {m : ℕ} {nrOf : T → ℕ}


-- @@ L228-280 verbatim
/-- **A tag-branched machinery's rules are definable**: the witness reads by
the read kit, the branch checkpoint by the dispatch shape – one dispatch per
tag, each guarded by the caller's decoding question – and the loops by
`DescriptiveComplexity.Draw.uRulesDefinable_elemRule`. -/
theorem uRulesDefinable_tagRule {wk rg : W} {emb : TagPh m T nrOf → P}
    {rdTrackT : Fin m → W}
    {MatchT : Fin m → ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {setTagFlag : ∀ e : Env L, Fin m → Bool → (Q → e.α) → (W → e.α) → Q → e.α}
    {TagsAre : ∀ e : Env L, T → (Q → e.α) → Prop}
    {rdTrackE : (τ : T) → Fin (nrOf τ) → W}
    {MatchE : (τ : T) → Fin (nrOf τ) → ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {setFlagE : ∀ e : Env L, (τ : T) → Fin (nrOf τ) → Bool →
      (Q → e.α) → (W → e.α) → Q → e.α}
    {initEl advEl exitSt : ∀ e : Env L, T → (Q → e.α) → (W → e.α) → Q → e.α}
    {IsMaxEl : ∀ e : Env L, T → (Q → e.α) → Prop} {exitPh : P}
    (hMT : ∀ i, UGDefinable (MatchT i))
    (hsetT : ∀ (i : Fin m) (b : Bool), UStDefinable fun e => setTagFlag e i b)
    (hTags : ∀ τ, UGDefinable fun e f (_ : W → e.α) => TagsAre e τ f)
    (hME : ∀ (τ : T) (j : Fin (nrOf τ)), UGDefinable (MatchE τ j))
    (hsetE : ∀ (τ : T) (j : Fin (nrOf τ)) (b : Bool),
      UStDefinable fun e => setFlagE e τ j b)
    (hinit : ∀ τ, UStDefinable fun e => initEl e τ)
    (hadv : ∀ τ, UStDefinable fun e => advEl e τ)
    (hexit : ∀ τ, UStDefinable fun e => exitSt e τ)
    (hmax : ∀ τ, UGDefinable fun e f (_ : W → e.α) => IsMaxEl e τ f) :
    URulesDefinable fun e =>
      tagRule e.one wk rg emb rdTrackT (fun i => MatchT i e) (setTagFlag e)
        (TagsAre e) rdTrackE (fun τ j => MatchE τ j e) (setFlagE e) (initEl e)
        (advEl e) (exitSt e) (IsMaxEl e) exitPh := by
  have hstay : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g => ¬(g wk = e.one) :=
    (uGDefinable_trkOne (L := L) (Q := Q) wk).not
  have hg : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g =>
      g wk = e.one ∧ g rg ≠ e.one :=
    (uGDefinable_trkOne (L := L) (Q := Q) wk).and
      (uGDefinable_trkOne (L := L) (Q := Q) rg).not
  rintro (i | - | ⟨τ, s⟩) ρ
  · match ρ with
    | Sum.inl σ => exact ReadKit.uRuleDefinable (hMT i) σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hg (hsetT i b) fun _ _ _ => rfl
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ hstay (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dsp τ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ (hg.and (hTags τ)) (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · exact uRulesDefinable_elemRule (wk := wk) (rg := rg)
      (emb := fun p => emb (TagPh.loopP τ p)) (rdTrack := rdTrackE τ)
      (exitPh := exitPh) (hME τ) (fun j b => hsetE τ j b) (hinit τ)
      (hadv τ) (hexit τ) (hmax τ) s ρ


-- @@ L282-282 verbatim
end Tag


-- @@ L284-284 verbatim
/-! ### The tuple loop -/


-- @@ L286-286 verbatim
section Tuple


-- @@ L288-315 verbatim
/-- **A tuple loop's stages are definable**: the read trip storing its bit and
the write trip handing it back. -/
theorem uRulesDefinable_tupleStageRule [DecidableEq W] {wk rg tSrc tDst : W}
    {emb : ChainPh 3 TuplePS → P}
    {MatchS MatchD : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {bitFlag : ∀ e : Env L, (Q → e.α) → Prop}
    {setBit : ∀ e : Env L, Bool → (Q → e.α) → (W → e.α) → Q → e.α}
    (hS : UGDefinable MatchS) (hD : UGDefinable MatchD)
    (hbit : UGDefinable fun e f (_ : W → e.α) => bitFlag e f)
    (hset : ∀ b : Bool, UStDefinable fun e => setBit e b) :
    URulesDefinable (Q := Q) fun e =>
      tupleStageRule e.zero e.one wk rg emb tSrc tDst (MatchS e) (MatchD e)
        (bitFlag e) (setBit e) := by
  have hg : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g =>
      g wk = e.one ∧ g rg ≠ e.one :=
    (uGDefinable_trkOne (L := L) (Q := Q) wk).and
      (uGDefinable_trkOne (L := L) (Q := Q) rg).not
  rintro (- | -) ρ
  · match ρ with
    | Sum.inl σ => exact ReadKit.uRuleDefinable hS σ
    | Sum.inr b =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hg (hset b) fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact WriteKit.uRuleDefinable hD hbit σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ hg (fun _ _ _ => rfl) fun _ _ _ => rfl


-- @@ L317-350 verbatim
/-- **A tuple loop's dispatch descriptors are definable**: begin, hand over,
advance or leave. -/
theorem uPreDefinable_tupleDsp {wk rg : W} {emb : ChainPh 3 TuplePS → P}
    {initLv advLv : ∀ e : Env L, (Q → e.α) → (W → e.α) → Q → e.α}
    {IsMaxLv : ∀ e : Env L, (Q → e.α) → Prop} {exitPh : P}
    (hinit : UStDefinable initLv) (hadv : UStDefinable advLv)
    (hmax : UGDefinable fun e f (_ : W → e.α) => IsMaxLv e f)
    (k : Fin 3) (b : Bool) :
    UPreDefinable fun e =>
      tupleDsp e.one wk rg emb (initLv e) (advLv e) (IsMaxLv e) exitPh k b := by
  have hg : UGDefinable (L := L) (Q := Q) fun e (_ : Q → e.α) g =>
      g wk = e.one ∧ g rg ≠ e.one :=
    (uGDefinable_trkOne (L := L) (Q := Q) wk).and
      (uGDefinable_trkOne (L := L) (Q := Q) rg).not
  have hkeep : UTrDefinable (L := L) (Q := Q) (W := W) fun _ _ g => g :=
    uTrDefinable_id
  match k, b with
  | ⟨0, _⟩, false =>
    exact ⟨⟨_, fun _ => rfl⟩, ⟨true, fun _ => iff_of_true trivial rfl⟩, hg, hinit, hkeep⟩
  | ⟨0, _⟩, true =>
    exact ⟨⟨_, fun _ => rfl⟩, ⟨false, fun _ => iff_of_false not_false Bool.false_ne_true⟩,
      uGDefinable_false, uStDefinable_id, hkeep⟩
  | ⟨1, _⟩, false =>
    exact ⟨⟨_, fun _ => rfl⟩, ⟨true, fun _ => iff_of_true trivial rfl⟩, hg,
      uStDefinable_id, hkeep⟩
  | ⟨1, _⟩, true =>
    exact ⟨⟨_, fun _ => rfl⟩, ⟨false, fun _ => iff_of_false not_false Bool.false_ne_true⟩,
      uGDefinable_false, uStDefinable_id, hkeep⟩
  | ⟨2, _⟩, false =>
    exact ⟨⟨_, fun _ => rfl⟩, ⟨true, fun _ => iff_of_true trivial rfl⟩,
      hg.and hmax.not, hadv, hkeep⟩
  | ⟨2, _⟩, true =>
    exact ⟨⟨_, fun _ => rfl⟩, ⟨true, fun _ => iff_of_true trivial rfl⟩,
      hg.and hmax, uStDefinable_id, hkeep⟩


-- @@ L352-370 verbatim
/-- **A tuple loop's rules are definable**, the chain over its two stages. -/
theorem uRulesDefinable_tupleRule [DecidableEq W] {wk rg tSrc tDst : W}
    {emb : ChainPh 3 TuplePS → P}
    {MatchS MatchD : ∀ e : Env L, (Q → e.α) → (W → e.α) → Prop}
    {bitFlag : ∀ e : Env L, (Q → e.α) → Prop}
    {setBit : ∀ e : Env L, Bool → (Q → e.α) → (W → e.α) → Q → e.α}
    {initLv advLv : ∀ e : Env L, (Q → e.α) → (W → e.α) → Q → e.α}
    {IsMaxLv : ∀ e : Env L, (Q → e.α) → Prop} {exitPh : P}
    (hS : UGDefinable MatchS) (hD : UGDefinable MatchD)
    (hbit : UGDefinable fun e f (_ : W → e.α) => bitFlag e f)
    (hset : ∀ b : Bool, UStDefinable fun e => setBit e b)
    (hinit : UStDefinable initLv) (hadv : UStDefinable advLv)
    (hmax : UGDefinable fun e f (_ : W → e.α) => IsMaxLv e f) :
    URulesDefinable (Q := Q) fun e =>
      tupleRule e.zero e.one wk rg emb tSrc tDst (MatchS e) (MatchD e)
        (bitFlag e) (setBit e) (initLv e) (advLv e) (IsMaxLv e) exitPh :=
  uRulesDefinable_chainRule
    (uRulesDefinable_tupleStageRule hS hD hbit hset)
    (uPreDefinable_tupleDsp hinit hadv hmax)


-- @@ L372-372 verbatim
end Tuple


-- @@ L374-374 verbatim
end Draw


-- @@ L376-376 verbatim
end DescriptiveComplexity
