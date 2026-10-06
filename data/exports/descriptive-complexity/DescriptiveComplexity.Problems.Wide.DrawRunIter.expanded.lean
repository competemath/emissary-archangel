/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRunElem
import DescriptiveComplexity.Problems.Wide.DrawRunTagged
import DescriptiveComplexity.Problems.Wide.DrawRunTuple


-- @@ L10-28 verbatim
/-!
# Generated control families: the runs, iterated

The run theorems of the layer take their control evolution as abstract
*families* over the enumeration – `fsOf a j`, the pointer before the `j`-th
read of round `a` – tied together by per-cover equations. An instantiation
has to produce such a family, and its rounds are defined by *iteration*: the
next round's entry is a function of the previous round's exit. This file
builds the family once, for every instantiation:

* `DescriptiveComplexity.Draw.iterOrd` – a state iterated along a finite
  linear order, by recursion on `DescriptiveComplexity.orank` (the bottom is
  the base, each cover one step);
* `DescriptiveComplexity.Draw.chainSt` – the within-round read chain, each
  read's stored bit chosen classically;
* `DescriptiveComplexity.Draw.elem_run_iter` – the element loop's run at the
  generated family: the caller supplies only the name guards at the
  generated states, the exhaustion conditions, and the geometry.
-/


-- @@ L30-30 verbatim
namespace DescriptiveComplexity


-- @@ L32-32 verbatim
namespace Draw


-- @@ L34-34 verbatim
open FirstOrder


-- @@ L36-36 verbatim
open Language Structure


-- @@ L38-38 verbatim
/-! ### Iteration along a finite linear order -/


-- @@ L40-40 verbatim
section Iter


-- @@ L42-42 verbatim
variable {ι : Type} {Q' : Type*} [LinearOrder ι] [Finite ι]


-- @@ L44-51 verbatim
open Classical in
/-- The iterated state at a rank: the base at `0`, one step per rank – the
element of that rank supplying the step's index. -/
noncomputable def iterState (init : Q') (step : ι → Q' → Q') : ℕ → Q'
  | 0 => init
  | n + 1 =>
    if h : ∃ a : ι, orank a = n then step h.choose (iterState init step n)
    else iterState init step n


-- @@ L53-56 verbatim
/-- **A state iterated along the order**: the base at the bottom, one step
per cover. -/
noncomputable def iterOrd (init : Q') (step : ι → Q' → Q') (a : ι) : Q' :=
  iterState init step (orank a)


-- @@ L58-63 verbatim
omit [Finite ι] in
/-- At the bottom the iteration is the base. -/
theorem iterOrd_bot {init : Q'} {step : ι → Q' → Q'} {a₀ : ι}
    (hbot : ∀ b, a₀ ≤ b) : iterOrd init step a₀ = init := by
  rw [iterOrd, orank_eq_zero hbot]
  rfl


-- @@ L65-76 verbatim
/-- Across a cover the iteration steps once, at the covered element. -/
theorem iterOrd_covers {init : Q'} {step : ι → Q' → Q'} {a a' : ι}
    (hlt : a < a') (hnb : ∀ b, ¬(a < b ∧ b < a')) :
    iterOrd init step a' = step a (iterOrd init step a) := by
  classical
  have hcov : a ⋖ a' := ⟨hlt, fun c h1 h2 => hnb c ⟨h1, h2⟩⟩
  have hrk : orank a' = orank a + 1 := orank_covBy hcov
  have hex : ∃ b : ι, orank b = orank a := ⟨a, rfl⟩
  rw [iterOrd, hrk]
  simp only [iterState]
  rw [dite_eq_left hex, orank_inj hex.choose_spec]
  rfl


-- @@ L78-96 verbatim
omit [Finite ι] in
/-- **An invariant of the step is an invariant of the iteration**: what the
base satisfies and every step preserves holds at every element. This is what
a threaded tape family's field lemmas are proved by – the fields a round
leaves alone are preserved by each step, hence along the whole loop. -/
theorem iterOrd_invariant {init : Q'} {step : ι → Q' → Q'} {Inv : Q' → Prop}
    (hinit : Inv init) (hstep : ∀ a q, Inv q → Inv (step a q)) (a : ι) :
    Inv (iterOrd init step a) := by
  classical
  have key : ∀ n : ℕ, Inv (iterState init step n) := by
    intro n
    induction n with
    | zero => exact hinit
    | succ n ih =>
      rw [iterState]
      split
      · exact hstep _ _ ih
      · exact ih
  exact key (orank a)


-- @@ L98-98 verbatim
end Iter


-- @@ L100-100 verbatim
/-! ### The within-round read chain -/


-- @@ L102-102 verbatim
section Chain


-- @@ L104-104 verbatim
variable {Q' : Type} {nr : ℕ}


-- @@ L106-116 verbatim
open Classical in
/-- **The read chain of one round**: the `j`-th prefix of the reads applied
to the round's entry state, each stored bit the read's. -/
noncomputable def chainSt (bit : Fin nr → Prop) (upd : Fin nr → Bool → Q' → Q')
    (base : Q') : ℕ → Q'
  | 0 => base
  | j + 1 =>
    if h : j < nr then
      upd ⟨j, h⟩ (if bit ⟨j, h⟩ then true else false)
        (chainSt bit upd base j)
    else chainSt bit upd base j


-- @@ L118-120 verbatim
@[simp]
theorem chainSt_zero {bit : Fin nr → Prop} {upd : Fin nr → Bool → Q' → Q'}
    {base : Q'} : chainSt bit upd base 0 = base := rfl


-- @@ L122-129 verbatim
/-- A positive read's link. -/
theorem chainSt_succ_pos {bit : Fin nr → Prop} {upd : Fin nr → Bool → Q' → Q'}
    {base : Q'} {j : ℕ} (h : j < nr) (hb : bit ⟨j, h⟩) :
    chainSt bit upd base (j + 1) =
      upd ⟨j, h⟩ true (chainSt bit upd base j) := by
  classical
  simp only [chainSt]
  rw [dite_eq_left h, ite_eq_left hb]


-- @@ L131-138 verbatim
/-- A negative read's link. -/
theorem chainSt_succ_neg {bit : Fin nr → Prop} {upd : Fin nr → Bool → Q' → Q'}
    {base : Q'} {j : ℕ} (h : j < nr) (hb : ¬bit ⟨j, h⟩) :
    chainSt bit upd base (j + 1) =
      upd ⟨j, h⟩ false (chainSt bit upd base j) := by
  classical
  simp only [chainSt]
  rw [dite_eq_left h, ite_eq_right hb]


-- @@ L140-140 verbatim
end Chain


-- @@ L142-142 verbatim
/-! ### The element loop's run, at the generated family -/


-- @@ L144-144 verbatim
section ElemIter


-- @@ L146-146 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L147-147 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L148-148 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L149-149 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L150-150 verbatim
variable {PR : Prog A R P Q W K dd} {nr : ℕ}

-- @@ L151-151 verbatim
variable {I : Type} {ile : I → I → Prop}

-- @@ L152-152 verbatim
variable (RF : IxFile (Univ A R P K dd) I ile)

-- @@ L153-153 verbatim
variable {wk rg : W} {emb : ElemPh nr → P}

-- @@ L154-154 verbatim
variable {rdTrack : Fin nr → W}

-- @@ L155-155 verbatim
variable {MatchOf : Fin nr → (Q → A) → (W → A) → Prop}

-- @@ L156-156 verbatim
variable {setFlag : Fin nr → Bool → (Q → A) → (W → A) → (Q → A)}

-- @@ L157-157 verbatim
variable {initEl advEl exitSt : (Q → A) → (W → A) → (Q → A)}

-- @@ L158-158 verbatim
variable {IsMaxEl : (Q → A) → Prop}

-- @@ L159-159 verbatim
variable {exitPh : P}

-- @@ L160-160 verbatim
variable {rEmb : ∀ i : ElemSite nr, ElemSh nr i → R}

-- @@ L161-161 verbatim
variable {ι : Type} [LinearOrder ι] [Finite ι]

-- @@ L162-162 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A}

-- @@ L163-163 verbatim
variable {v : Univ A R P K dd → Prop}

-- @@ L164-164 verbatim
variable {m : Fin nr → I → Prop}


-- @@ L166-174 verbatim
variable (setFlag initEl advEl rest v m) in
/-- **The generated round-entry state**: the loop's `initEl` at the bottom,
each cover the previous round's reads folded and advanced. -/
noncomputable def elemIter (xOf : ι → Fin nr → I) (f₀ : Q → A)
    (a : ι) : Q → A :=
  iterOrd (initEl f₀ (rest v))
    (fun a q =>
      advEl (chainSt (fun j => m j (xOf a j))
        (fun j b q' => setFlag j b q' (rest v)) q nr) (rest v)) a


-- @@ L176-183 verbatim
variable (setFlag initEl advEl rest v m) in
/-- **The generated within-round family**: the read chain of round `a`
applied to its entry state. -/
noncomputable def elemFam (xOf : ι → Fin nr → I) (f₀ : Q → A)
    (a : ι) (j : Fin (nr + 1)) : Q → A :=
  chainSt (fun j' => m j' (xOf a j'))
    (fun j' b q' => setFlag j' b q' (rest v))
    (elemIter setFlag initEl advEl rest v m xOf f₀ a) (j : ℕ)


-- @@ L185-189 verbatim
/-! **The background is read at the working cell alone.** Both generated
families mention `rest` only as `rest v`, so a background that moves
elsewhere – at a register cell, say, where the four register slots live –
generates the same control. This is what makes a loop blind to the two
scratch registers of the state it is run at. -/


-- @@ L191-191 verbatim
section CongrRest


-- @@ L193-193 verbatim
variable {rest' : (Univ A R P K dd → Prop) → W → A}


-- @@ L195-205 verbatim
omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- Two backgrounds agreeing at the working cell give one round-entry
family. -/
theorem elemIter_congr_rest (h : rest v = rest' v)
    (xOf : ι → Fin nr → I) (f₀ : Q → A) (a : ι) :
    elemIter setFlag initEl advEl rest v m xOf f₀ a =
      elemIter setFlag initEl advEl rest' v m xOf f₀ a := by
  simp only [elemIter, h]


-- @@ L207-218 verbatim
omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- Two backgrounds agreeing at the working cell give one within-round
family. -/
theorem elemFam_congr_rest (h : rest v = rest' v)
    (xOf : ι → Fin nr → I) (f₀ : Q → A) (a : ι)
    (j : Fin (nr + 1)) :
    elemFam setFlag initEl advEl rest v m xOf f₀ a j =
      elemFam setFlag initEl advEl rest' v m xOf f₀ a j := by
  simp only [elemFam, h, elemIter_congr_rest h]


-- @@ L220-220 verbatim
end CongrRest


-- @@ L222-224 verbatim
variable (hrules : ∀ (i : ElemSite nr) (ρ : ElemSh nr i),
  PR.rules (rEmb i ρ) = elemRule PR.one wk rg emb rdTrack MatchOf setFlag
    initEl advEl exitSt IsMaxEl exitPh i ρ)

-- @@ L225-225 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L226-226 verbatim
variable (hix : IsLinOrd ile)

-- @@ L227-227 verbatim
variable {gbot : I} (hbot : ∀ y, ile gbot y)

-- @@ L228-228 verbatim
variable {v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (RF.cell gbot))

-- @@ L229-229 verbatim
variable (hvi : WMIncr WMLe v v')

-- @@ L230-230 verbatim
variable (hwkS : ∀ r, rest r wk = bitVal PR.zero PR.one (r = v))

-- @@ L231-232 verbatim
variable (hrg : ∀ r, rest r rg =
  bitVal PR.zero PR.one (∃ u : I, r = RF.cell u))

-- @@ L233-234 verbatim
variable (hm : ∀ (j : Fin nr) (r : Univ A R P K dd → Prop),
  rest r (rdTrack j) = bitVal PR.zero PR.one (bitAtOf RF.cell (m j) r))

-- @@ L235-235 verbatim
variable (hnewk : ∀ j, wk ≠ rdTrack j) (hnerg : ∀ j, rg ≠ rdTrack j)

-- @@ L236-236 verbatim
variable {t₀ : W} {m₀ : I → Prop}

-- @@ L237-237 verbatim
variable (hm₀ : ∀ r, rest r t₀ = bitVal PR.zero PR.one (bitAtOf RF.cell m₀ r))

-- @@ L238-238 verbatim
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)

-- @@ L239-239 verbatim
variable {a₀ aT : ι}

-- @@ L240-240 verbatim
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)

-- @@ L241-241 verbatim
variable (xOf : ι → Fin nr → I) (f₀ : Q → A)

-- @@ L242-244 verbatim
variable (hname : ∀ (a : ι) (j : Fin nr),
  MatchOf j (elemFam setFlag initEl advEl rest v m xOf f₀ a j.castSucc)
    (PR.passTracksAt RF.cell (rdTrack j) rest (m j) (RF.cell (xOf a j))))

-- @@ L245-247 verbatim
variable (huniq : ∀ (a : ι) (j : Fin nr) (r : Univ A R P K dd → Prop),
  MatchOf j (elemFam setFlag initEl advEl rest v m xOf f₀ a j.castSucc)
    (PR.passTracksAt RF.cell (rdTrack j) rest (m j) r) → r = RF.cell (xOf a j))

-- @@ L248-248 verbatim
variable (hmaxT : IsMaxEl (elemFam setFlag initEl advEl rest v m xOf f₀ aT (Fin.last nr)))

-- @@ L249-250 verbatim
variable (hmaxF : ∀ a, a < aT →
  ¬IsMaxEl (elemFam setFlag initEl advEl rest v m xOf f₀ a (Fin.last nr)))


-- @@ L252-286 verbatim
include RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀ hwkt₀ hrgt₀
  hbotI htopI hname huniq hmaxT hmaxF in
/-- **The element loop's run at the generated family, on a clock**: only the
name guards at the generated states, the exhaustion conditions and the geometry
are owed; the family equations hold by construction. -/
theorem elem_reachesIn_iter (c : ℕ)
    (hcost : ∀ (a : ι) (j : Fin nr),
      2 * (wideRank (RF.cell (xOf a j)) - wideRank v) + 2 ≤ c) :
    (wideData (Univ A R P K dd)).ReachesIn ((2 + (c + 2) * nr) * (Nat.card ι + 1) + 1)
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (exitSt (elemFam setFlag initEl advEl rest v m xOf f₀ aT (Fin.last nr))
            (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  refine elem_reachesIn RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀
    hwkt₀ hrgt₀ hbotI htopI
    (fun a => elemFam setFlag initEl advEl rest v m xOf f₀ a (Fin.last nr))
    (elemFam setFlag initEl advEl rest v m xOf f₀) (fun _ => rfl) xOf hname huniq
    ?_ ?_ ?_ hmaxT hmaxF c hcost ?_
  · intro a j hbit
    exact chainSt_succ_pos j.isLt (by
      exact (show m j (xOf a j) from hbit))
  · intro a j hbit
    exact chainSt_succ_neg j.isLt hbit
  · intro a a' hlt hnb
    exact (iterOrd_covers (init := initEl f₀ (rest v))
      (step := fun a q => advEl (chainSt (fun j => m j (xOf a j))
        (fun j b q' => setFlag j b q' (rest v)) q nr) (rest v))
      hlt hnb).symm
  · exact (iterOrd_bot (init := initEl f₀ (rest v))
      (step := fun a q => advEl (chainSt (fun j => m j (xOf a j))
        (fun j b q' => setFlag j b q' (rest v)) q nr) (rest v))
      hbotI).symm


-- @@ L288-308 verbatim
include RF hrules hR hlin hix hbot hv hvi hwkS hrg hm hnewk hnerg hm₀ hwkt₀ hrgt₀
  hbotI htopI hname huniq hmaxT hmaxF in
/-- **The element loop's run at the generated family**, the budget forgotten. -/
theorem elem_run_iter :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb .e0) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (exitSt (elemFam setFlag initEl advEl rest v m xOf f₀ aT (Fin.last nr))
            (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ :=
  (elem_reachesIn_iter (RF := RF) (hrules := hrules) (hR := hR) (hlin := hlin)
    (hix := hix) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkS := hwkS) (hrg := hrg)
    (hm := hm) (hnewk := hnewk) (hnerg := hnerg) (hm₀ := hm₀) (hwkt₀ := hwkt₀)
    (hrgt₀ := hrgt₀) (hbotI := hbotI) (htopI := htopI) (hname := hname)
    (huniq := huniq) (hmaxT := hmaxT) (hmaxF := hmaxF)
    (c := 2 * Nat.card {q : WPoint (Univ A R P K dd) //
      (wideData (Univ A R P K dd)).Posn q} + 2)
    (hcost := fun a j => by
      have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xOf a j))
      omega)).reflTransGen


-- @@ L310-310 verbatim
end ElemIter


-- @@ L312-312 verbatim
/-! ### The tag-branched machinery's run, at the generated families -/


-- @@ L314-314 verbatim
section TagIter


-- @@ L316-316 verbatim
variable {A R P Q W K T : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L317-317 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L318-318 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L319-319 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L320-320 verbatim
variable {PR : Prog A R P Q W K dd} {m : ℕ} {nrOf : T → ℕ}

-- @@ L321-321 verbatim
variable {I : Type} {ile : I → I → Prop}

-- @@ L322-322 verbatim
variable (RF : IxFile (Univ A R P K dd) I ile)

-- @@ L323-323 verbatim
variable {wk rg : W} {emb : TagPh m T nrOf → P}

-- @@ L324-324 verbatim
variable {rdTrackT : Fin m → W}

-- @@ L325-325 verbatim
variable {MatchT : Fin m → (Q → A) → (W → A) → Prop}

-- @@ L326-326 verbatim
variable {setTagFlag : Fin m → Bool → (Q → A) → (W → A) → (Q → A)}

-- @@ L327-327 verbatim
variable {TagsAre : T → (Q → A) → Prop}

-- @@ L328-328 verbatim
variable {rdTrackE : (τ : T) → Fin (nrOf τ) → W}

-- @@ L329-329 verbatim
variable {MatchE : (τ : T) → Fin (nrOf τ) → (Q → A) → (W → A) → Prop}

-- @@ L330-330 verbatim
variable {setFlagE : (τ : T) → Fin (nrOf τ) → Bool → (Q → A) → (W → A) → (Q → A)}

-- @@ L331-331 verbatim
variable {initEl advEl exitSt : T → (Q → A) → (W → A) → (Q → A)}

-- @@ L332-332 verbatim
variable {IsMaxEl : T → (Q → A) → Prop}

-- @@ L333-333 verbatim
variable {exitPh : P}

-- @@ L334-334 verbatim
variable {rest : (Univ A R P K dd → Prop) → W → A}

-- @@ L335-335 verbatim
variable {v : Univ A R P K dd → Prop}

-- @@ L336-336 verbatim
variable {mT : Fin m → I → Prop}


-- @@ L338-344 verbatim
variable (setTagFlag rest v mT) in
/-- **The generated witness chain**: the `i`-th prefix of the witness reads
applied to the entry control, each one-hot bit the read's. -/
noncomputable def tagFam (xT : Fin m → I) (f₀ : Q → A)
    (i : Fin (m + 1)) : Q → A :=
  chainSt (fun i' => mT i' (xT i'))
    (fun i' b q => setTagFlag i' b q (rest v)) f₀ (i : ℕ)


-- @@ L346-356 verbatim
omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] in
/-- **The witness chain reads its background at the working cell alone.** -/
theorem tagFam_congr_rest {rest' : (Univ A R P K dd → Prop) → W → A}
    (h : rest v = rest' v) (xT : Fin m → I) (f₀ : Q → A)
    (i : Fin (m + 1)) :
    tagFam setTagFlag rest v mT xT f₀ i =
      tagFam setTagFlag rest' v mT xT f₀ i := by
  simp only [tagFam, h]


-- @@ L358-358 verbatim
variable {rEmb : ∀ i : TagSite m T nrOf, TagSh m T nrOf i → R}

-- @@ L359-361 verbatim
variable (hrules : ∀ (i : TagSite m T nrOf) (ρ : TagSh m T nrOf i),
  PR.rules (rEmb i ρ) = tagRule PR.one wk rg emb rdTrackT MatchT setTagFlag
    TagsAre rdTrackE MatchE setFlagE initEl advEl exitSt IsMaxEl exitPh i ρ)

-- @@ L362-362 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L363-363 verbatim
variable (hix : IsLinOrd ile)

-- @@ L364-364 verbatim
variable {gbot : I} (hbot : ∀ y, ile gbot y)

-- @@ L365-365 verbatim
variable {v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (RF.cell gbot))

-- @@ L366-366 verbatim
variable (hvi : WMIncr WMLe v v')

-- @@ L367-367 verbatim
variable (hwkS : ∀ r, rest r wk = bitVal PR.zero PR.one (r = v))

-- @@ L368-369 verbatim
variable (hrg : ∀ r, rest r rg =
  bitVal PR.zero PR.one (∃ u : I, r = RF.cell u))

-- @@ L370-371 verbatim
variable (hmT : ∀ (i : Fin m) (r : Univ A R P K dd → Prop),
  rest r (rdTrackT i) = bitVal PR.zero PR.one (bitAtOf RF.cell (mT i) r))

-- @@ L372-372 verbatim
variable (hnewkT : ∀ i, wk ≠ rdTrackT i) (hnergT : ∀ i, rg ≠ rdTrackT i)

-- @@ L373-373 verbatim
variable {t₀ : W} {m₀ : I → Prop}

-- @@ L374-374 verbatim
variable (hm₀ : ∀ r, rest r t₀ = bitVal PR.zero PR.one (bitAtOf RF.cell m₀ r))

-- @@ L375-375 verbatim
variable (hwkt₀ : wk ≠ t₀) (hrgt₀ : rg ≠ t₀)

-- @@ L376-376 verbatim
variable (xT : Fin m → I) (f₀ : Q → A)

-- @@ L377-379 verbatim
variable (hnameT : ∀ i : Fin m,
  MatchT i (tagFam setTagFlag rest v mT xT f₀ i.castSucc)
    (PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) (RF.cell (xT i))))

-- @@ L380-382 verbatim
variable (huniqT : ∀ (i : Fin m) (r : Univ A R P K dd → Prop),
  MatchT i (tagFam setTagFlag rest v mT xT f₀ i.castSucc)
    (PR.passTracksAt RF.cell (rdTrackT i) rest (mT i) r) → r = RF.cell (xT i))

-- @@ L383-383 verbatim
variable {τ : T}

-- @@ L384-384 verbatim
variable (hτ : TagsAre τ (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)))

-- @@ L385-385 verbatim
variable {mE : Fin (nrOf τ) → I → Prop}

-- @@ L386-387 verbatim
variable (hmE : ∀ (j : Fin (nrOf τ)) (r : Univ A R P K dd → Prop),
  rest r (rdTrackE τ j) = bitVal PR.zero PR.one (bitAtOf RF.cell (mE j) r))

-- @@ L388-388 verbatim
variable (hnewkE : ∀ j, wk ≠ rdTrackE τ j) (hnergE : ∀ j, rg ≠ rdTrackE τ j)

-- @@ L389-389 verbatim
variable {ι : Type} [LinearOrder ι] [Finite ι] {a₀ aT : ι}

-- @@ L390-390 verbatim
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)

-- @@ L391-391 verbatim
variable (xE : ι → Fin (nrOf τ) → I)

-- @@ L392-395 verbatim
variable (hnameE : ∀ (a : ι) (j : Fin (nrOf τ)),
  MatchE τ j (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a j.castSucc)
    (PR.passTracksAt RF.cell (rdTrackE τ j) rest (mE j) (RF.cell (xE a j))))

-- @@ L396-399 verbatim
variable (huniqE : ∀ (a : ι) (j : Fin (nrOf τ)) (r : Univ A R P K dd → Prop),
  MatchE τ j (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a j.castSucc)
    (PR.passTracksAt RF.cell (rdTrackE τ j) rest (mE j) r) → r = RF.cell (xE a j))

-- @@ L400-402 verbatim
variable (hmaxT : IsMaxEl τ
  (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
    (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) aT (Fin.last (nrOf τ))))

-- @@ L403-405 verbatim
variable (hmaxF : ∀ a, a < aT → ¬IsMaxEl τ
  (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
    (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a (Fin.last (nrOf τ))))


-- @@ L407-455 verbatim
include RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀ hwkt₀ hrgt₀
  hnameT huniqT hτ hmE hnewkE hnergE hbotI htopI hnameE huniqE hmaxT hmaxF in
/-- **The tag-branched machinery's run at the generated families, on a
clock**: the witness chain and the branch's element loop are both generated, so
only the name guards, the branch decode and the exhaustion conditions are owed,
and the cost is the chain's reads plus the branch's whole loop. -/
theorem tag_reachesIn_iter (c : ℕ)
    (hcostT : ∀ i : Fin m, 2 * (wideRank (RF.cell (xT i)) - wideRank v) + 2 ≤ c)
    (hcostE : ∀ (a : ι) (j : Fin (nrOf τ)),
      2 * (wideRank (RF.cell (xE a j)) - wideRank v) + 2 ≤ c) :
    (wideData (Univ A R P K dd)).ReachesIn
      ((c + 2) * m + 2 + ((2 + (c + 2) * nrOf τ) * (Nat.card ι + 1) + 1))
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (exitSt τ (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
            (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) aT
            (Fin.last (nrOf τ))) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ := by
  classical
  refine tag_reachesIn RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀
    hwkt₀ hrgt₀ (tagFam setTagFlag rest v mT xT f₀) xT hnameT huniqT
    ?_ ?_ c hcostT hτ hmE hnewkE hnergE hbotI htopI
    (fun a => elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) a (Fin.last (nrOf τ)))
    (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
      (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)))
    (fun _ => rfl) xE hnameE huniqE ?_ ?_ ?_ hmaxT hmaxF ?_ hcostE
  · intro i hbit
    exact chainSt_succ_pos i.isLt (show mT i (xT i) from hbit)
  · intro i hbit
    exact chainSt_succ_neg i.isLt hbit
  · intro a j hbit
    exact chainSt_succ_pos j.isLt (show mE j (xE a j) from hbit)
  · intro a j hbit
    exact chainSt_succ_neg j.isLt hbit
  · intro a a' hlt hnb
    exact (iterOrd_covers
      (init := initEl τ (tagFam setTagFlag rest v mT xT f₀ (Fin.last m))
        (rest v))
      (step := fun a q => advEl τ (chainSt (fun j => mE j (xE a j))
        (fun j b q' => setFlagE τ j b q' (rest v)) q (nrOf τ)) (rest v))
      hlt hnb).symm
  · exact (iterOrd_bot
      (init := initEl τ (tagFam setTagFlag rest v mT xT f₀ (Fin.last m))
        (rest v))
      (step := fun a q => advEl τ (chainSt (fun j => mE j (xE a j))
        (fun j b q' => setFlagE τ j b q' (rest v)) q (nrOf τ)) (rest v))
      hbotI).symm


-- @@ L457-484 verbatim
include RF hrules hR hlin hix hbot hv hvi hwkS hrg hmT hnewkT hnergT hm₀ hwkt₀ hrgt₀
  hnameT huniqT hτ hmE hnewkE hnergE hbotI htopI hnameE huniqE hmaxT hmaxF in
/-- **The tag-branched machinery's run at the generated families**, the budget
forgotten. -/
theorem tag_run_iter :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (tagFirstRd emb) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (exitSt τ (elemFam (setFlagE τ) (initEl τ) (advEl τ) rest v mE xE
            (tagFam setTagFlag rest v mT xT f₀ (Fin.last m)) aT
            (Fin.last (nrOf τ))) (rest v))), Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell t₀ rest m₀) (PR.syElt PR.blank)⟩ :=
  (tag_reachesIn_iter (RF := RF) (hrules := hrules) (hR := hR) (hlin := hlin)
    (hix := hix) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkS := hwkS) (hrg := hrg)
    (hmT := hmT) (hnewkT := hnewkT) (hnergT := hnergT) (hm₀ := hm₀)
    (hwkt₀ := hwkt₀) (hrgt₀ := hrgt₀) (hnameT := hnameT) (huniqT := huniqT)
    (hτ := hτ) (hmE := hmE) (hnewkE := hnewkE) (hnergE := hnergE)
    (hbotI := hbotI) (htopI := htopI) (hnameE := hnameE) (huniqE := huniqE)
    (hmaxT := hmaxT) (hmaxF := hmaxF)
    (c := 2 * Nat.card {q : WPoint (Univ A R P K dd) //
      (wideData (Univ A R P K dd)).Posn q} + 2)
    (hcostT := fun i => by
      have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xT i))
      omega)
    (hcostE := fun a j => by
      have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xE a j))
      omega)).reflTransGen


-- @@ L486-486 verbatim
end TagIter


-- @@ L488-488 verbatim
/-! ### The tuple loop's run, at the generated families -/


-- @@ L490-490 verbatim
section TupleIter


-- @@ L492-492 verbatim
variable {A R P Q W K : Type} {dd : ℕ} [Fintype Q] [Fintype W] [DecidableEq W]

-- @@ L493-493 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P] [LinearOrder K]

-- @@ L494-494 verbatim
variable [Language.wide.Structure (Univ A R P K dd)]

-- @@ L495-495 verbatim
variable [Finite A] [Finite R] [Finite P] [Finite K]

-- @@ L496-496 verbatim
variable {PR : Prog A R P Q W K dd}

-- @@ L497-497 verbatim
variable {I : Type} {ile : I → I → Prop}

-- @@ L498-498 verbatim
variable (RF : IxFile (Univ A R P K dd) I ile)

-- @@ L499-499 verbatim
variable {wk rg : W} {emb : ChainPh 3 TuplePS → P}

-- @@ L500-500 verbatim
variable {tSrc tDst : W}

-- @@ L501-501 verbatim
variable {MatchS MatchD : (Q → A) → (W → A) → Prop}

-- @@ L502-502 verbatim
variable {bitFlag : (Q → A) → Prop}

-- @@ L503-503 verbatim
variable {setBit : Bool → (Q → A) → (W → A) → (Q → A)}

-- @@ L504-504 verbatim
variable {initLv advLv : (Q → A) → (W → A) → (Q → A)}

-- @@ L505-505 verbatim
variable {IsMaxLv : (Q → A) → Prop}

-- @@ L506-506 verbatim
variable {exitPh : P}

-- @@ L507-507 verbatim
variable {ι : Type} [LinearOrder ι] [Finite ι]

-- @@ L508-508 verbatim
variable {mSrc : I → Prop}

-- @@ L509-509 verbatim
variable {v : Univ A R P K dd → Prop}

-- @@ L510-511 verbatim
variable {restF : (I → Prop) →
  (Univ A R P K dd → Prop) → W → A}


-- @@ L513-519 verbatim
variable (mSrc) in
/-- **The generated destination track**: empty of the loop's bits at the
bottom, each cover the round's copy applied. -/
noncomputable def tupleIterD (xS xD : ι → I)
    (mD₀ : I → Prop) (a : ι) : I → Prop :=
  iterOrd mD₀
    (fun a' m => fun y => (y = xD a' ∧ mSrc (xS a')) ∨ (y ≠ xD a' ∧ m y)) a


-- @@ L521-533 verbatim
variable (setBit initLv advLv restF mSrc v) in
open Classical in
/-- **The generated pre-store control**: the loop's `initLv` at the bottom,
each cover the previous round folded and advanced, the round's symbol read
from the destination-dependent background. -/
noncomputable def tupleIter0 (xS xD : ι → I)
    (mD₀ : I → Prop) (f₀ : Q → A) (a : ι) : Q → A :=
  iterOrd (initLv f₀ (restF mD₀ v))
    (fun a' q =>
      advLv (if mSrc (xS a') then setBit true q (restF
          (tupleIterD mSrc xS xD mD₀ a') v)
        else setBit false q (restF (tupleIterD mSrc xS xD mD₀ a') v))
        (restF (tupleIterD mSrc xS xD mD₀ a') v)) a


-- @@ L535-545 verbatim
variable (setBit initLv advLv restF mSrc v) in
open Classical in
/-- **The generated post-store control**: the round's bit stored. -/
noncomputable def tupleIter1 (xS xD : ι → I)
    (mD₀ : I → Prop) (f₀ : Q → A) (a : ι) : Q → A :=
  if mSrc (xS a) then
    setBit true (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
      (restF (tupleIterD mSrc xS xD mD₀ a) v)
  else
    setBit false (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
      (restF (tupleIterD mSrc xS xD mD₀ a) v)


-- @@ L547-547 verbatim
section CongrRestF


-- @@ L549-550 verbatim
variable {restF' : (I → Prop) →
  (Univ A R P K dd → Prop) → W → A}


-- @@ L552-563 verbatim
omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- **The copy loop reads its background at the working cell alone** – at
every destination content, the cell being the same one. -/
theorem tupleIter0_congr_restF (h : ∀ m', restF m' v = restF' m' v)
    (xS xD : ι → I) (mD₀ : I → Prop)
    (f₀ : Q → A) (a : ι) :
    tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a =
      tupleIter0 setBit initLv advLv mSrc v restF' xS xD mD₀ f₀ a := by
  simp only [tupleIter0, h]


-- @@ L565-575 verbatim
omit [Fintype Q] [Fintype W] [DecidableEq W] [LinearOrder A] [LinearOrder R]
  [LinearOrder P] [LinearOrder K]
  [Language.wide.Structure (Univ A R P K dd)] [Finite A] [Finite R]
  [Finite P] [Finite K] [Finite ι] in
/-- The same, after the round's store. -/
theorem tupleIter1_congr_restF (h : ∀ m', restF m' v = restF' m' v)
    (xS xD : ι → I) (mD₀ : I → Prop)
    (f₀ : Q → A) (a : ι) :
    tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a =
      tupleIter1 setBit initLv advLv mSrc v restF' xS xD mD₀ f₀ a := by
  simp only [tupleIter1, h, tupleIter0_congr_restF h]


-- @@ L577-577 verbatim
end CongrRestF


-- @@ L579-579 verbatim
variable {rEmb : ∀ i : ChainSite 3 TupleSS, ChainSh 3 TupleSS TupleSh i → R}

-- @@ L580-582 verbatim
variable (hrules : ∀ (i : ChainSite 3 TupleSS) (ρ : ChainSh 3 TupleSS TupleSh i),
  PR.rules (rEmb i ρ) = tupleRule PR.zero PR.one wk rg emb tSrc tDst MatchS
    MatchD bitFlag setBit initLv advLv IsMaxLv exitPh i ρ)

-- @@ L583-583 verbatim
variable (hR : PR.table.Reads) (hlin : IsLinOrd (WMLe (A := Univ A R P K dd)))

-- @@ L584-584 verbatim
variable (hix : IsLinOrd ile)

-- @@ L585-585 verbatim
variable {gbot : I} (hbot : ∀ y, ile gbot y)

-- @@ L586-586 verbatim
variable {v' : Univ A R P K dd → Prop} (hv : WMSetLt WMLe v (RF.cell gbot))

-- @@ L587-587 verbatim
variable (hvi : WMIncr WMLe v v')

-- @@ L588-588 verbatim
variable {a₀ aT : ι}

-- @@ L589-589 verbatim
variable (hbotI : ∀ a, a₀ ≤ a) (htopI : ∀ a, a ≤ aT)

-- @@ L590-590 verbatim
variable (xS xD : ι → I)

-- @@ L591-591 verbatim
variable (mD₀ : I → Prop) (f₀ : Q → A)

-- @@ L592-592 verbatim
variable (hwkS : ∀ m' r, restF m' r wk = bitVal PR.zero PR.one (r = v))

-- @@ L593-594 verbatim
variable (hrg : ∀ m' r, restF m' r rg =
  bitVal PR.zero PR.one (∃ u : I, r = RF.cell u))

-- @@ L595-596 verbatim
variable (hsrc : ∀ m' r, restF m' r tSrc =
  bitVal PR.zero PR.one (bitAtOf RF.cell mSrc r))

-- @@ L597-598 verbatim
variable (hdst : ∀ m' r, restF m' r tDst =
  bitVal PR.zero PR.one (bitAtOf RF.cell m' r))

-- @@ L599-599 verbatim
variable (hoff : ∀ m₁ m₂ r s, s ≠ tDst → restF m₁ r s = restF m₂ r s)

-- @@ L600-600 verbatim
variable (hwkSrc : wk ≠ tSrc) (hwkDst : wk ≠ tDst)

-- @@ L601-601 verbatim
variable (hrgSrc : rg ≠ tSrc) (hrgDst : rg ≠ tDst)

-- @@ L602-605 verbatim
variable (hnameS : ∀ a, MatchS
  (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
  (PR.passTracksAt RF.cell tSrc (restF (tupleIterD mSrc xS xD mD₀ a)) mSrc
    (RF.cell (xS a))))

-- @@ L606-609 verbatim
variable (huniqS : ∀ (a : ι) (r : Univ A R P K dd → Prop),
  MatchS (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
    (PR.passTracksAt RF.cell tSrc (restF (tupleIterD mSrc xS xD mD₀ a)) mSrc r) →
      r = RF.cell (xS a))

-- @@ L610-613 verbatim
variable (hnameD : ∀ a, MatchD
  (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
  (PR.passTracksAt RF.cell tDst (restF (tupleIterD mSrc xS xD mD₀ a))
    (tupleIterD mSrc xS xD mD₀ a) (RF.cell (xD a))))

-- @@ L614-617 verbatim
variable (huniqD : ∀ (a : ι) (r : Univ A R P K dd → Prop),
  MatchD (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
    (PR.passTracksAt RF.cell tDst (restF (tupleIterD mSrc xS xD mD₀ a))
      (tupleIterD mSrc xS xD mD₀ a) r) → r = RF.cell (xD a))

-- @@ L618-620 verbatim
variable (hbitFlag : ∀ a,
  bitFlag (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a) ↔
    mSrc (xS a))

-- @@ L621-622 verbatim
variable (hmaxT : IsMaxLv
  (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ aT))

-- @@ L623-624 verbatim
variable (hmaxF : ∀ a, a < aT →
  ¬IsMaxLv (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a))


-- @@ L626-679 verbatim
include RF hrules hR hlin hix hbot hv hvi hbotI htopI hwkS hrg hsrc hdst hoff
  hwkSrc hwkDst hrgSrc hrgDst hnameS huniqS hnameD huniqD hbitFlag
  hmaxT hmaxF in
/-- **The tuple loop's run at the generated families, on a clock**: only the
name guards, the copied-bit read-back and the exhaustion conditions are owed,
and the cost is a round's width once per tuple of the enumeration. -/
theorem tuple_reachesIn_iter (w : ℕ)
    (hcost : ∀ a : ι, 2 * (wideRank (RF.cell (xS a)) - wideRank v) + 2 ≤ w ∧
      2 * (wideRank (RF.cell (xD a)) - wideRank v) + 2 ≤ w) :
    (wideData (Univ A R P K dd)).ReachesIn ((2 * w + 8) * (Nat.card ι + 1) + 1)
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨0, by omega⟩)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell tSrc (restF (tupleIterD mSrc xS xD mD₀ a₀))
          mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ aT)),
        Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell tDst (restF (tupleIterD mSrc xS xD mD₀ aT))
          (tuplePost mSrc (tupleIterD mSrc xS xD mD₀) xS xD aT))
          (PR.syElt PR.blank)⟩ := by
  classical
  refine tuple_reachesIn RF hrules hR hlin hix hbot hv hvi hbotI htopI
    (restOf := fun a => restF (tupleIterD mSrc xS xD mD₀ a))
    (mD := tupleIterD mSrc xS xD mD₀)
    (fun a r => hwkS _ r) (fun a r => hrg _ r) (fun a r => hsrc _ r)
    (fun a r => hdst _ r) hwkSrc hwkDst hrgSrc hrgDst xS xD
    (tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀)
    (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀)
    hnameS huniqS hnameD huniqD ?_ ?_ hbitFlag ?_ ?_ ?_ hmaxT hmaxF w hcost ?_
  · intro a hb
    rw [tupleIter1, ite_eq_left hb]
  · intro a hb
    rw [tupleIter1, ite_eq_right hb]
  · intro a a' hlt hnb
    have hcov : tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a' =
        advLv (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a)
          (restF (tupleIterD mSrc xS xD mD₀ a) v) := by
      rw [tupleIter1]
      exact iterOrd_covers hlt hnb
    exact hcov.symm
  · intro a a' hlt hnb y
    have hcov : tupleIterD mSrc xS xD mD₀ a' = fun y =>
        (y = xD a ∧ mSrc (xS a)) ∨
        (y ≠ xD a ∧ tupleIterD mSrc xS xD mD₀ a y) :=
      iterOrd_covers hlt hnb
    rw [hcov]
    exact Iff.rfl
  · intro a a' hlt hnb r s hs
    exact hoff _ _ r s hs
  · have hD0 : tupleIterD mSrc xS xD mD₀ a₀ = mD₀ :=
      iterOrd_bot hbotI
    have hI0 : tupleIter0 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ a₀ =
        initLv f₀ (restF mD₀ v) :=
      iterOrd_bot hbotI
    rw [hD0, hI0]


-- @@ L681-708 verbatim
include RF hrules hR hlin hix hbot hv hvi hbotI htopI hwkS hrg hsrc hdst hoff
  hwkSrc hwkDst hrgSrc hrgDst hnameS huniqS hnameD huniqD hbitFlag
  hmaxT hmaxF in
/-- **The tuple loop's run at the generated families**, the budget forgotten. -/
theorem tuple_run_iter :
    Relation.ReflTransGen (wideData (Univ A R P K dd)).Step
      ⟨Sum.inr (PR.stElt (emb (.chk ⟨0, by omega⟩)) f₀), Sum.inl v,
        wideTape (PR.trackTapeAt RF.cell tSrc (restF (tupleIterD mSrc xS xD mD₀ a₀))
          mSrc) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt exitPh
          (tupleIter1 setBit initLv advLv mSrc v restF xS xD mD₀ f₀ aT)),
        Sum.inl v',
        wideTape (PR.trackTapeAt RF.cell tDst (restF (tupleIterD mSrc xS xD mD₀ aT))
          (tuplePost mSrc (tupleIterD mSrc xS xD mD₀) xS xD aT))
          (PR.syElt PR.blank)⟩ :=
  (tuple_reachesIn_iter (RF := RF) (hrules := hrules) (hR := hR) (hlin := hlin)
    (hix := hix) (hbot := hbot) (hv := hv) (hvi := hvi) (hbotI := hbotI)
    (htopI := htopI) (hwkS := hwkS) (hrg := hrg) (hsrc := hsrc) (hdst := hdst)
    (hoff := hoff) (hwkSrc := hwkSrc) (hwkDst := hwkDst) (hrgSrc := hrgSrc)
    (hrgDst := hrgDst) (hnameS := hnameS) (huniqS := huniqS) (hnameD := hnameD)
    (huniqD := huniqD) (hbitFlag := hbitFlag) (hmaxT := hmaxT) (hmaxF := hmaxF)
    (w := 2 * Nat.card {q : WPoint (Univ A R P K dd) //
      (wideData (Univ A R P K dd)).Posn q} + 2)
    (hcost := fun a => ⟨by
        have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xS a))
        omega, by
        have := wideRank_lt_card (A := Univ A R P K dd) (RF.cell (xD a))
        omega⟩)).reflTransGen


-- @@ L710-710 verbatim
/-! ### The destination track, in closed form -/


-- @@ L712-712 verbatim
section TupleContent


-- @@ L714-714 verbatim
variable {A R P K : Type} {dd : ℕ}

-- @@ L715-715 verbatim
variable {ι : Type} [LinearOrder ι] [Finite ι]


-- @@ L717-737 verbatim
/-- **What the copy loop can hold**: every cell of the destination track is
either one the loop wrote – a destination cell of some round – or one it
started with. A property of cells closed under both is therefore closed
under the whole loop; that is how the target of a random access is known to
be an address of argument cells alone. -/
theorem tupleIterD_of_mem {mSrc : I → Prop}
    {xS xD : ι → I} {mD₀ : I → Prop}
    (Q : I → Prop) (hxD : ∀ a : ι, Q (xD a))
    (h₀ : ∀ y, mD₀ y → Q y) (b : ι) {y : I}
    (hy : tupleIterD mSrc xS xD mD₀ b y) : Q y := by
  induction b using order_induction with
  | hmin z hz =>
    rw [show tupleIterD mSrc xS xD mD₀ z = mD₀ from iterOrd_bot hz] at hy
    exact h₀ y hy
  | hstep w z hwz hnb ih =>
    rw [show tupleIterD mSrc xS xD mD₀ z = fun y =>
      (y = xD w ∧ mSrc (xS w)) ∨ (y ≠ xD w ∧ tupleIterD mSrc xS xD mD₀ w y)
      from iterOrd_covers hwz hnb] at hy
    rcases hy with ⟨rfl, -⟩ | ⟨-, hw⟩
    · exact hxD w
    · exact ih hw


-- @@ L739-789 verbatim
/-- **What the copy loop has written**: a cell holds a bit exactly when some
earlier round wrote it – that round's source bit – or it held one from the
start and no round has touched it. The destination cells being distinct is
what makes the disjunction honest: a cell is written at most once. -/
theorem tupleIterD_iff {mSrc : I → Prop}
    {xS xD : ι → I}
    (hinj : ∀ u u' : ι, xD u = xD u' → u = u')
    {mD₀ : I → Prop} (b : ι) (y : I) :
    tupleIterD mSrc xS xD mD₀ b y ↔
      ((∃ u < b, y = xD u ∧ mSrc (xS u)) ∨
        ((∀ u < b, y ≠ xD u) ∧ mD₀ y)) := by
  induction b using order_induction with
  | hmin z hz =>
    have hz0 : tupleIterD mSrc xS xD mD₀ z = mD₀ := iterOrd_bot hz
    have hnou : ∀ u : ι, ¬u < z := fun u hu =>
      absurd (hz u) (not_le_of_gt hu)
    rw [hz0]
    constructor
    · intro h
      exact Or.inr ⟨fun u hu => absurd hu (hnou u), h⟩
    · rintro (⟨u, hu, -⟩ | ⟨-, h⟩)
      · exact absurd hu (hnou u)
      · exact h
  | hstep w z hwz hnb ih =>
    have hz2 : tupleIterD mSrc xS xD mD₀ z = fun y =>
        (y = xD w ∧ mSrc (xS w)) ∨ (y ≠ xD w ∧ tupleIterD mSrc xS xD mD₀ w y) :=
      iterOrd_covers hwz hnb
    have hltz : ∀ u : ι, u < z ↔ u ≤ w := fun u =>
      ⟨fun h => le_of_not_gt fun hgt => hnb u ⟨hgt, h⟩,
        fun h => lt_of_le_of_lt h hwz⟩
    rw [hz2]
    constructor
    · rintro (⟨hy, hsrc⟩ | ⟨hne, hw⟩)
      · exact Or.inl ⟨w, hwz, hy, hsrc⟩
      · rcases ih.mp hw with ⟨u, hu, hy, hsrc⟩ | ⟨hno, hm⟩
        · exact Or.inl ⟨u, lt_trans hu hwz, hy, hsrc⟩
        · refine Or.inr ⟨fun u hu => ?_, hm⟩
          rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
          · exact hno u h
          · rw [h]
            exact hne
    · rintro (⟨u, hu, hy, hsrc⟩ | ⟨hno, hm⟩)
      · rcases lt_or_eq_of_le ((hltz u).mp hu) with h | h
        · refine Or.inr ⟨?_, ih.mpr (Or.inl ⟨u, h, hy, hsrc⟩)⟩
          intro hc
          rw [hy] at hc
          exact absurd (hinj u w hc) (ne_of_lt h)
        · rw [h] at hy hsrc
          exact Or.inl ⟨hy, hsrc⟩
      · refine Or.inr ⟨hno w hwz, ih.mpr (Or.inr
          ⟨fun u hu => hno u (lt_trans hu hwz), hm⟩)⟩


-- @@ L791-791 verbatim
end TupleContent


-- @@ L793-793 verbatim
end TupleIter


-- @@ L795-795 verbatim
end Draw


-- @@ L797-797 verbatim
end DescriptiveComplexity
