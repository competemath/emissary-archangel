/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxVerdict
import DescriptiveComplexity.Problems.Wide.DrawIxPack
import DescriptiveComplexity.Problems.Wide.DrawSpineSem
import DescriptiveComplexity.Problems.Wide.DrawIxEval


-- @@ L11-17 verbatim
/-!
# What the spine does to the tape, at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawSpineSem` read at a coarse file: what a
whole spine leaves on the tape at one address, the sweep's fold over the
addresses, and the semantic packs the positions are run with.
-/


-- @@ L19-19 verbatim
namespace DescriptiveComplexity


-- @@ L21-21 verbatim
namespace Draw


-- @@ L23-23 verbatim
open FirstOrder


-- @@ L25-25 verbatim
open Language Structure


-- @@ L27-27 verbatim
namespace Data


-- @@ L29-29 verbatim
variable {L : Language.{0, 0}} (dt : Data L) {A R : Type}

-- @@ L30-30 verbatim
variable [Fintype dt.SlotIx]

-- @@ L31-31 verbatim
variable [LinearOrder A] [LinearOrder R]

-- @@ L32-32 verbatim
variable {P : Type}

-- @@ L33-33 verbatim
variable [LinearOrder (P)]

-- @@ L34-35 verbatim
variable [Language.wide.Structure
  (Univ A R (P) dt.KIx dt.dd)]

-- @@ L36-36 verbatim
variable [Finite A] [Finite R] [Finite (P)]

-- @@ L37-38 verbatim
variable {PR : Prog A R (P) dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}

-- @@ L39-39 verbatim
variable {I : Type} [Finite I]

-- @@ L40-40 verbatim
variable (F : LaidFile dt A R (P) I)

-- @@ L41-41 verbatim
variable {elt : I → Univ A R (P) dt.KIx dt.dd}

-- @@ L42-42 verbatim
variable (hinj : Function.Injective elt)

-- @@ L43-43 verbatim
variable (hhasP : F.toLayout.HasName PR.zero)

-- @@ L44-45 verbatim
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))

-- @@ L46-46 verbatim
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)

-- @@ L47-47 verbatim
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)

-- @@ L48-48 verbatim
variable {e₀ : Univ A R (P) dt.KIx dt.dd}

-- @@ L49-49 verbatim
variable (he₀ : ∀ y, WMLe e₀ y)

-- @@ L50-50 verbatim
variable {Use : I → Prop}

-- @@ L51-51 verbatim
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))

-- @@ L52-55 verbatim
variable (hup : ∀ (u : I) (x : Univ A R (P) dt.KIx dt.dd),
  Use u → WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.

-- @@ L56-57 verbatim
variable (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)

-- @@ L58-59 verbatim
variable [Nonempty A] [L.IsRelational] [L.Structure A]
-- The marks-to-shapes bridge at a coarse file (see `DrawIxRoundSem`).

-- @@ L60-70 verbatim
variable (hpassEnc : ∀ (vi : dt.VarIx)
    (stV : TapeSt dt A R (P) I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ ↔
    IsEnc dt.ly PR.zero PR.one (wmBlk (ixAddr elt stV.val)
      (Tag.arg (toLex (dt.igBlk vi ℓ)) :
        Tag R (P) dt.KIx)))
-- The gates' marks-to-shapes bridge at a coarse file: a position is gated
-- exactly when the blocks of its mirror's **address** below the variable's
-- arity are encodings. Free at the elementwise file
-- (`DescriptiveComplexity.Draw.Data.isEnc_of_gatedAt` and its converse).

-- @@ L71-80 verbatim
variable (hgateEnc : ∀ (j : Fin dt.nv)
    (st : TapeSt dt A R (P) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st ↔
    ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      IsEnc dt.ly PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx)))

-- @@ L81-81 verbatim
variable [Finite dt.KIx]


-- @@ L83-83 verbatim
/-! ### One position's write -/


-- @@ L85-85 verbatim
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}


-- @@ L87-87 verbatim
/-! ### The spine's writes -/


-- @@ L89-89 verbatim
section Spine


-- @@ L91-91 verbatim
variable {mOf : Fin dt.nv → (I → Prop)}

-- @@ L92-93 verbatim
variable {stOf : Fin (dt.nv + 1) →
  TapeSt dt A R (P) I}

-- @@ L94-94 verbatim
variable {bOf : Fin dt.nv → Prop}

-- @@ L95-96 verbatim
variable (hst : ∀ j : Fin dt.nv, stOf j.succ =
  dt.ixPostVarSt v (stOf j.castSucc) (mOf j) (dt.varList.get j) (bOf j))


-- @@ L98-114 verbatim
open Classical in
/-- **The only thing the `new` tracks need of a position**: its own cell at
the marker holds its verdict and every other cell rides. Weaker than the
cover equation `hst`, and weaker on purpose – a *branched* position's leg
is not literally a
`DescriptiveComplexity.Draw.Data.ixPostVarSt` of the position's entry
state (its VAL loop may normalize the two scratch registers first), while
this projection of it is
(`DescriptiveComplexity.Draw.Data.ixLegStB_new`). -/
abbrev IxWritesNew
    (stOf : Fin (dt.nv + 1) → TapeSt dt A R (P) I)
    (bOf : Fin dt.nv → Prop) : Prop :=
  ∀ (j : Fin dt.nv) (i' : dt.d.B.ι)
    (r : Univ A R (P) dt.KIx dt.dd → Prop),
    (stOf j.succ).new i' r =
      (if i' = dt.varList.get j ∧ r = v then bOf j
        else (stOf j.castSucc).new i' r)


-- @@ L116-116 verbatim
variable (hstN : dt.IxWritesNew (v := v) stOf bOf)


-- @@ L118-139 verbatim
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- **Anything a position's write leaves alone rides the whole spine**: the
induction along the positions, once, for every field but `val` and `new`. -/
theorem ixSpineRide {β : Sort _}
    (G : TapeSt dt A R (P) I → β)
    (hF : ∀ st m i b, G (dt.ixPostVarSt v st m i b) = G st)
    (k : Fin (dt.nv + 1)) :
    G (stOf k) = G (stOf 0) := by
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := hst ⟨n, hnv⟩
    exact Eq.trans (congrArg G hstep) (Eq.trans (hF _ _ _ _) (ih _))


-- @@ L141-151 verbatim
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hst in
/-- The working address rides the spine. -/
theorem ixSpine_mir (k : Fin (dt.nv + 1)) : (stOf k).mir = (stOf 0).mir :=
  dt.ixSpineRide hst (fun st => st.mir) (fun _ _ _ _ => rfl) k


-- @@ L153-179 verbatim
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hstN in
/-- **Off the marker, the `new` tracks ride the spine**: a position writes
its own cell only. -/
theorem ixSpine_new_off (k : Fin (dt.nv + 1)) (i : dt.d.B.ι)
    {r : Univ A R (P) dt.KIx dt.dd → Prop}
    (hr : r ≠ v) : (stOf k).new i r ↔ (stOf 0).new i r := by
  classical
  obtain ⟨n, hn⟩ := k
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
    have hstep := hstN ⟨n, hnv⟩ i r
    have hsucc : (⟨n, hnv⟩ : Fin dt.nv).succ = ⟨n + 1, hn⟩ := rfl
    have hcast : (⟨n, hnv⟩ : Fin dt.nv).castSucc =
        ⟨n, Nat.lt_succ_of_lt hnv⟩ := rfl
    rw [hsucc, hcast] at hstep
    exact (iff_of_eq (hstep.trans
      (ite_eq_right (fun h : i = dt.varList.get ⟨n, hnv⟩ ∧ r = v => hr h.2)))).trans
      (ih _)


-- @@ L181-222 verbatim
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hstN in
/-- **At the marker, a variable's `new` cell is the verdict of its own
position**: it is written there, and no later position writes it, the
enumeration being duplicate-free. -/
theorem ixNew_last_get (j : Fin dt.nv) :
    (stOf (Fin.last dt.nv)).new (dt.varList.get j) v ↔ bOf j := by
  classical
  have key : ∀ (n : ℕ) (hn : n < dt.nv + 1) (j : Fin dt.nv), (j : ℕ) < n →
      ((stOf ⟨n, hn⟩).new (dt.varList.get j) v ↔ bOf j) := by
    intro n
    induction n with
    | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn j hj
      have hnv : n < dt.nv := Nat.lt_of_succ_lt_succ hn
      have hcong := hstN ⟨n, hnv⟩ (dt.varList.get j) v
      have hsucc : (⟨n, hnv⟩ : Fin dt.nv).succ = ⟨n + 1, hn⟩ := rfl
      have hcast : (⟨n, hnv⟩ : Fin dt.nv).castSucc =
          ⟨n, Nat.lt_succ_of_lt hnv⟩ := rfl
      rw [hsucc, hcast] at hcong
      rcases Nat.lt_or_ge (j : ℕ) n with hlt | hge
      · -- an earlier position: this write is at another variable
        have hne : dt.varList.get j ≠ dt.varList.get ⟨n, hnv⟩ := by
          intro hc
          have hjj : j = (⟨n, hnv⟩ : Fin dt.nv) := varList_get_inj hc
          exact absurd (congrArg Fin.val hjj) (show (j : ℕ) ≠ n by omega)
        exact (iff_of_eq (hcong.trans (ite_eq_right
          (fun h : dt.varList.get j = dt.varList.get ⟨n, hnv⟩ ∧ v = v =>
            hne h.1)))).trans (ih _ j hlt)
      · -- this very position
        have hjn : j = (⟨n, hnv⟩ : Fin dt.nv) :=
          Fin.ext (show (j : ℕ) = n by omega)
        subst hjn
        exact iff_of_eq (hcong.trans (ite_eq_left ⟨rfl, rfl⟩))
  exact key dt.nv (Nat.lt_succ_self _) j j.isLt


-- @@ L224-241 verbatim
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)]
  [Language.wide.Structure
    (Univ A R (P) dt.KIx dt.dd)]
  [Finite A] [Finite R] [Finite (P)]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
include hstN in
/-- **At an address every position rejects, the marker's `new` cells are
all clear** – the junk legs
(`DescriptiveComplexity.Draw.Data.ixVarLegFail_reachesIn`,
`DescriptiveComplexity.Draw.Data.ixVarLegUngated_reachesIn`) store `False`, which
is what the stage dictionary holds at an address that encodes no tuple. -/
theorem ixNew_last_of_false (hbOf : ∀ j : Fin dt.nv, ¬bOf j)
    (i : dt.d.B.ι) : ¬(stOf (Fin.last dt.nv)).new i v := by
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  exact fun hc => hbOf j ((dt.ixNew_last_get hstN j).mp hc)


-- @@ L243-243 verbatim
end Spine


-- @@ L245-245 verbatim
/-! ### The spine's semantic reading -/


-- @@ L247-247 verbatim
section SpineNext


-- @@ L249-249 verbatim
variable [LinearOrder (dt.X.Map A)]

-- @@ L250-250 verbatim
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

-- @@ L251-251 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L252-252 verbatim
variable (mV : ιV → I → Prop)

-- @@ L253-253 verbatim
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)


-- @@ L255-353 verbatim
include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **After the spine, one variable's `new` cell holds its own step of the
iteration** – the per-position form: only the position of that variable, its
pack and its verdict are named, so an address where *other* positions are
junk is covered too (which is what a sweep needs, the gates being per
variable). -/
theorem ixNew_last_next_at
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : Tag R (P) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (P) I}
    {bOf : Fin dt.nv → Prop} (j : Fin dt.nv)
    (semOfJ : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b))
    (fG : dt.CtlIx → A)
    (hstN : dt.IxWritesNew (v := v) stOf bOf)
    (hmirOf : (stOf j.castSucc).mir = (stOf 0).mir)
    (holdOf : (stOf j.castSucc).old = (stOf 0).old)
    (hbj : bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP (dt.varAt j) (stOf j.castSucc) v mV semOfJ
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP
              (dt.varAt j) (stOf j.castSucc) v mV semOfJ fG aT) aT)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf j.castSucc) (mV aT)) v)))
    (mbW : Fin (dt.arOf (dt.varAt j)) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.ixMirBlk (elt := elt) (stOf 0) (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R (P) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf 0).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt (stOf j.castSucc) (mV a) with sav := ixMark elt v }
        (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (ixAddr elt (dt.ixRoundSt (stOf j.castSucc) (mV a)).mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx) =
          encMap dt.ly PR.zero PR.one (mbW ℓ)),
      semOfJ a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc) (dt.varAt j)
        (dt.ixRoundSt (stOf j.castSucc) (mV a)) hp mbW hmb' b) :
    (stOf (Fin.last dt.nv)).new (dt.varList.get j) v ↔
      dt.d.next σ (dt.varList.get j) mbW := by
  classical
  have hmbj : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.ixMirBlk (elt := elt) (stOf j.castSucc)
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ) := fun ℓ =>
    (congrFun (ixMirBlk_of_mir (elt := elt) hmirOf) _).trans (hmb _)
  have hdictj : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf j.castSucc).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x) :=
    fun iv x hs => (iff_of_eq (congrFun (congrFun holdOf iv) _)).trans
      (hdict iv x hs)
  refine (dt.ixNew_last_get hstN j).trans (hbj.trans ?_)
  exact ixAccVerdict_next (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc)
    (st := stOf j.castSucc) (mV := mV) (i := dt.varList.get j) (semOf := semOfJ)
    (hlin := hlin) (hord := hord) (hbotV := hbotV) (hmV0 := hmV0)
    (hUse := hUse) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
    (mbW := mbW) (hmb := hmbj) (hdict := hdictj) (hbelow := hbelow)
    (hordP := hordP) (hsem := fun a hp b => hsem a hp b _) (fG := fG)


-- @@ L355-450 verbatim
include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **After the spine, every `new` track holds the next stage at the
address's points.** The position of a variable writes its verdict, which
`DescriptiveComplexity.Draw.Data.ixAccVerdict_next` reads as
`DescriptiveComplexity.StepDef.next`; the mirror and the dictionary ride
the spine, so the semantic hypotheses need only be given at the entry
state. -/
theorem ixNew_last_next
    (hlin : IsLinOrd (WMLe (A := Univ A R (P)
      dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd,
      WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV)
      (t : Tag R (P) dt.KIx)
      (w : Fin dt.dd → A), ixAddr elt (mV a) (t, w) →
        ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {stOf : Fin (dt.nv + 1) →
      TapeSt dt A R (P) I}
    {bOf : Fin dt.nv → Prop}
    (semOfJ : ∀ (j : Fin dt.nv) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) elt (dt.kindOf (dt.varAt j) b))
    (fGOf : Fin dt.nv → dt.CtlIx → A)
    (hstN : dt.IxWritesNew (v := v) stOf bOf)
    (hmirOf : ∀ k : Fin (dt.nv + 1), (stOf k).mir = (stOf 0).mir)
    (holdOf : ∀ k : Fin (dt.nv + 1), (stOf k).old = (stOf 0).old)
    (hbOf : ∀ j : Fin dt.nv, bOf j ↔
      dt.accVerdict PR.one (dt.polOf (dt.varAt j))
        ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
            (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
            (dt.ixVarFM (elt := elt) F hinj hhasP heltP
              (dt.varAt j) (stOf j.castSucc) v mV (semOfJ j)
              (fGOf j) aT) aT)
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixRoundSt (stOf j.castSucc) (mV aT)) v)))
    (pt : Fin dt.ko → dt.X.Map A)
    (hpt : ∀ k : Fin dt.ko,
      dt.ixMirBlk (elt := elt) (stOf 0) k = encMap dt.ly PR.zero PR.one (pt k))
    {Below : (Univ A R (P) dt.KIx dt.dd →
      Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      ((stOf 0).old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (j : Fin dt.nv) (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (dt.varAt j) ts
        { dt.ixRoundSt (stOf j.castSucc) (mV a) with sav := ixMark elt v }
        (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (j : Fin dt.nv) (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
          (dt.ixRoundSt (stOf j.castSucc) (mV a)) ℓ)
      (b : Fin (dt.natOf (dt.varAt j)))
      (hmb' : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
        wmBlk (ixAddr elt (dt.ixRoundSt (stOf j.castSucc) (mV a)).mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R (P) dt.KIx) =
          encMap dt.ly PR.zero PR.one
            (pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))),
      semOfJ j a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc) (dt.varAt j)
        (dt.ixRoundSt (stOf j.castSucc) (mV a)) hp
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ)) hmb' b)
    (i : dt.d.B.ι) :
    (stOf (Fin.last dt.nv)).new i v ↔
      dt.d.next σ i
        (fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (some i)) ℓ)) := by
  classical
  obtain ⟨j, hj⟩ := dt.exists_varList_get i
  subst hj
  exact ixNew_last_next_at (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc) (mV := mV)
    (hUse := hUse) (hlin := hlin) (hord := hord) (hbotV := hbotV)
    (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
    (j := j) (semOfJ := semOfJ j) (fG := fGOf j) (hstN := hstN)
    (hmirOf := hmirOf j.castSucc) (holdOf := holdOf j.castSucc) (hbj := hbOf j)
    (mbW := fun ℓ => pt (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
    (hmb := fun ℓ => hpt _) (hdict := hdict) (hbelow := hbelow j)
    (hordP := hordP) (hsem := fun a hp b hmb' => hsem j a hp b hmb')


-- @@ L452-452 verbatim
end SpineNext


-- @@ L454-454 verbatim
/-! ### What a whole sweep leaves behind -/


-- @@ L456-456 verbatim
section SweepDict


-- @@ L458-458 verbatim
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}


-- @@ L460-460 verbatim
end SweepDict


-- @@ L462-462 verbatim
/-! ### The address's cell, in dictionary form -/


-- @@ L464-464 verbatim
section AddrDict


-- @@ L466-466 verbatim
variable [LinearOrder (dt.X.Map A)]

-- @@ L467-467 verbatim
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

-- @@ L468-468 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L469-469 verbatim
variable (mV : ιV → I → Prop)

-- @@ L470-470 verbatim
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)


-- @@ L472-472 verbatim
end AddrDict


-- @@ L474-474 verbatim
/-! ### The semantic pack, transported along the spine -/


-- @@ L476-476 verbatim
/-! ### The per-position families, built -/


-- @@ L478-478 verbatim
section Family


-- @@ L480-480 verbatim
variable [LinearOrder (dt.X.Map A)]

-- @@ L481-481 verbatim
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

-- @@ L482-482 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {aT : ιV}

-- @@ L483-483 verbatim
variable (mV : ιV → I → Prop)

-- @@ L484-484 verbatim
variable (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)

-- @@ L485-485 verbatim
variable (st₀ : TapeSt dt A R (P) I)

-- @@ L486-486 verbatim
variable (f₀ : dt.CtlIx → A)

-- @@ L487-492 verbatim
variable (sem₀ : ∀ (j : Fin dt.nv) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st₀ (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st₀ (mV a))
      elt (dt.kindOf (dt.varAt j) b))

-- @@ L493-493 verbatim
variable (tOf : ∀ j : Fin dt.nv, Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)


-- @@ L495-514 verbatim
/-- **One node of the spine**: the tape state, the proof that its mirror is
still the address's – which is what lets the *next* node build its pack –
and the control. The three have to be produced together: the pack a
position's leg needs is typed at that position's state, and is available
only because the mirror rode (`ixSpineSem`). -/
noncomputable def ixSpineNode :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNode n
    if h : n < dt.nv then
      let f' := dt.ixLegCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
        (dt.ixSpineSem F PR.zero PR.one (dt.varAt ⟨n, h⟩) mV (sem₀ ⟨n, h⟩)
          prev.2.1) prev.2.2
      ⟨dt.ixPostVarSt v prev.1 (mV aT) (dt.varList.get ⟨n, h⟩)
          ((dt.varArgsOf PR.zero PR.one (dt.varAt ⟨n, h⟩)).accBit f'),
        prev.2.1, f'⟩
    else prev


-- @@ L516-519 verbatim
/-- The tape family of the spine. -/
noncomputable def ixSpineStOf (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNode (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf (k : ℕ)).1


-- @@ L521-521 verbatim
/-! ### The per-position families, threaded -/


-- @@ L523-546 verbatim
/-- **One node of the spine, threaded**: as
`DescriptiveComplexity.Draw.Data.ixSpineNode`, with the leg's own exit
state – SAV and TARGET as its VAL loop left them – instead of the
normalized one. The mirror still rides, which is what makes the next
position's pack exist. -/
noncomputable def ixSpineNodeT :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNodeT n
    if h : n < dt.nv then
      ⟨dt.ixLegStT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.ixSpineSemT F PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2,
        (dt.ixLegStT_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.ixSpineSemT F PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2).1.trans prev.2.1,
        dt.ixLegCtlT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨n, h⟩ prev.1 (tOf ⟨n, h⟩)
          (dt.ixSpineSemT F PR.zero PR.one (dt.varAt ⟨n, h⟩) (v := v) mV
            (sem₀ ⟨n, h⟩) prev.2.1) prev.2.2⟩
    else prev


-- @@ L548-551 verbatim
/-- The threaded tape family of the spine. -/
noncomputable def ixSpineStOfT (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ sem₀ tOf (k : ℕ)).1


-- @@ L553-561 verbatim
omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The mirror rides the threaded family too** – by construction. -/
theorem ixSpineStOfT_mir (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ sem₀ tOf k).mir = st₀.mir :=
  (dt.ixSpineNodeT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ sem₀ tOf (k : ℕ)).2.1


-- @@ L563-579 verbatim
/-! ### The per-position families, branched

The threaded family above runs the gated leg at every position, which a
sweep cannot afford: it visits junk addresses too. The branched family
takes whichever of the three legs each position's own gates call for
(`DescriptiveComplexity.Draw.Data.ixLegStB`), and is otherwise the same
recursion – the mirror still rides, because no leg writes it.

Its semantic parameter is **not** the entry state's pack transported: it is
the *conditioned* family `DescriptiveComplexity.Draw.Data.ixGatedSem`
inhabits – a pack at every gated position of every state, at every address.
Conditioned, because at a junk position no pack exists (the argument blocks
encode nothing there); quantified over the address as well, because the sweep runs this spine at
`v := w` for an address `w` its own binders are fixed before. With that type the
parameter is supplied outright at the top – `fun w => dt.ixGatedSem hzo hlin
mV` – and no semantic assumption about a position survives in the run
layer. -/


-- @@ L581-591 verbatim
variable (semB : ∀ (w : Univ A R (P) dt.KIx
    dt.dd → Prop) (j : Fin dt.nv)
  (st : TapeSt dt A R (P) I),
  dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
  ∀ (p : IxScratch dt A R (P) I) (a : ιV),
  (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (dt.varAt j)),
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) w (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b))


-- @@ L593-607 verbatim
/-- **One node of the spine, branched**. -/
noncomputable def ixSpineNodeB :
    ℕ → Σ' st : TapeSt dt A R (P) I,
      PProd (st.mir = st₀.mir) (dt.CtlIx → A)
  | 0 => ⟨st₀, rfl, f₀⟩
  | n + 1 =>
    let prev := ixSpineNodeB n
    if h : n < dt.nv then
      ⟨dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2,
        (dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2).1.trans prev.2.1,
        dt.ixLegCtlB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV ⟨n, h⟩ prev.1
          (semB v ⟨n, h⟩ prev.1) prev.2.2⟩
    else prev


-- @@ L609-612 verbatim
/-- The branched tape family of the spine. -/
noncomputable def ixSpineStOfB (k : Fin (dt.nv + 1)) :
    TapeSt dt A R (P) I :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).1


-- @@ L614-616 verbatim
/-- The branched control family of the spine. -/
noncomputable def ixSpineFsOfB (k : Fin (dt.nv + 1)) : dt.CtlIx → A :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).2.2


-- @@ L618-625 verbatim
omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The mirror rides the branched family** – by construction. -/
theorem ixSpineStOfB_mir (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).mir = st₀.mir :=
  (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB (k : ℕ)).2.1


-- @@ L627-647 verbatim
omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The marker rides the branched family**: no leg writes the working
register, so the `hwkOf` a spine asks for is the entry state's. -/
theorem ixSpineStOfB_wk (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).wk = st₀.wk := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.wk = st₀.wk := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dite_eq_left hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.1).trans ih
      · rw [dite_eq_right hm]
        exact ih
  exact hn (k : ℕ)


-- @@ L649-669 verbatim
omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The bottom mark rides the branched family** – the `hbotOf` a spine asks
for. -/
theorem ixSpineStOfB_bot (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).bot = st₀.bot := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.bot = st₀.bot := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dite_eq_left hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.2.1).trans ih
      · rw [dite_eq_right hm]
        exact ih
  exact hn (k : ℕ)


-- @@ L671-694 verbatim
omit [Finite I] [Finite R] [Finite P] [Finite dt.KIx] [LinearOrder (dt.X.Map A)]
  [Finite ιV] in
/-- **The dictionary rides the branched family**: no leg of the evaluation
writes the `old` tracks, so the stage the spine reads at its last checkpoint is
the stage it was entered with. This is what lets a *guessing* program discharge
the output's `hdict`: what its guess wrote is what the verdict is read
against. -/
theorem ixSpineStOfB_old (k : Fin (dt.nv + 1)) :
    (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
      mV st₀ f₀ semB k).old = st₀.old := by
  have hn : ∀ n : ℕ, (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP
      heltP mV st₀ f₀ semB n).1.old = st₀.old := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [ixSpineNodeB]
      by_cases hm : m < dt.nv
      · rw [dite_eq_left hm]
        exact ((dt.ixLegStB_fields (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV ⟨m, hm⟩ _ _ _).2.2.2.1).trans ih
      · rw [dite_eq_right hm]
        exact ih
  exact hn (k : ℕ)


-- @@ L696-717 verbatim
/-- The packs of the branched family: the parameter's own, at the position's
state – the gate being what makes them exist. -/
noncomputable def ixSpineSemOfB (j : Fin dt.nv)
    (hg : dt.ixGatedAt (PR := PR) (elt := elt) F j
      (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
        mV st₀ f₀ semB j.castSucc))
    (p : IxScratch dt A R (P) I) (a : ιV)
    (hp : ∀ ℓ : Fin (dt.nIn (dt.varAt j)),
      dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB
          j.castSucc) p (mV a)) ℓ)
    (b : Fin (dt.natOf (dt.varAt j))) :
    dt.IxKindSem PR.zero PR.one (dt.varAt j)
      (dt.ixMatSt (elt := elt) (dt.varAt j)
        (dt.ixVarRdSt (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB
          j.castSucc) p (mV a)) v (b : ℕ))
      elt (dt.kindOf (dt.varAt j) b) :=
  semB v j (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB j.castSucc) hg p a
    hp b


-- @@ L719-735 verbatim
omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched control's cover equation** –
`DescriptiveComplexity.Draw.Data.nexIxSpineB_reachesIn`'s `hfs`. -/
theorem ixSpineFsOfB_succ (j : Fin dt.nv) :
    dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.succ =
      dt.ixLegCtlB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc)
        (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
        (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc) := by
  change (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB ((j : ℕ) + 1)).2.2 = _
  rw [ixSpineNodeB, dite_eq_left j.isLt]
  rfl


-- @@ L737-753 verbatim
omit [Finite R] [Finite (P)] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] [Finite ιV] in
omit [Finite I] in
/-- **The branched tape's cover equation** –
`DescriptiveComplexity.Draw.Data.nexIxSpineB_reachesIn`'s `hst`. -/
theorem ixSpineStOfB_succ (j : Fin dt.nv) :
    dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j.succ =
      dt.ixLegStB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV j
        (dt.ixSpineStOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc)
        (dt.ixSpineSemOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st₀ f₀ semB j)
        (dt.ixSpineFsOfB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
          mV st₀ f₀ semB j.castSucc) := by
  change (dt.ixSpineNodeB (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
    mV st₀ f₀ semB ((j : ℕ) + 1)).1 = _
  rw [ixSpineNodeB, dite_eq_left j.isLt]
  rfl


-- @@ L755-762 verbatim
/-! ### The branched spine's dictionary at one address

Gating is per variable, and so is the reading: at an address whose blocks
below a variable's arity all encode points, that variable's cell holds one
step of the iteration there; where one of them does not, the position takes
an ungated leg, writes `False`, and the dictionary is `False` too. Nothing
is assumed of the *other* variables' blocks – which is what a sweep needs,
since it passes every address. -/


-- @@ L764-809 verbatim
include hinj hhasP heltP hix hblkP hmono hup hpassEnc hUse in
omit [Finite I] [Finite dt.KIx] in
/-- **The verdict the output's leg leaves is the output sentence**, at the
stage the tracks hold. The output variable is nullary, so its blocks encode
the empty tuple and there is nothing to ask of them – which is why this is the
one verdict a program can take at the address its head starts on. This is the
`hacc` a run through the output's machinery
(`DescriptiveComplexity.Draw.Data.nexIxEvalOutB_reachesIn`) asks for, and the
reason the accepting bit says anything at all. -/
theorem ixOutAcc_iff_out
    (hlin : IsLinOrd (WMLe (A := Univ A R (P) dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R (P) dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a : ιV, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R (P) dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ jj : Fin dt.ki, t = argIn dt.ko jj)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (st : TapeSt dt A R (P) I)
    {Below : (Univ A R (P) dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P)
        (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP none ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v } (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (f₀ : dt.CtlIx → A) :
    (dt.varArgsOf PR.zero PR.one none).accBit
        (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf
          (fun a hp b => dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc)
            none (dt.ixRoundSt st (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
          f₀) ↔
      @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out :=
  dt.ixAccVerdict_out (elt := elt) (F := F) (hinj := hinj) (hhasP := hhasP)
    (heltP := heltP) (hix := hix) (hblkP := hblkP) (hmono := hmono) (hup := hup)
    (hpassEnc := hpassEnc) (st := st) (mV := mV) (hlin := hlin) (hord := hord)
    (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr)
    (hKin := hKin) (hTop := hTop) (σ := σ) (hdict := hdict) (hbelow := hbelow)
    (hordP := hordP) (hsem := fun _ _ _ => rfl) (fG := _)


-- @@ L811-811 verbatim
end Family


-- @@ L813-820 verbatim
/-! ### The sweep's families, over an arbitrary per-address leg

Everything the sweep's families need of an address's evaluation is *what
state and control it ends in*. Taking those two as parameters makes the
whole layer – the iteration, its two cover equations, and the ride lemmas
that discharge `reaches_sweep`'s `hwkE`/`hmirE`/`hltpE` – serve any
evaluation: the spine as first built, its threaded twin, and the branched
form a junk address will need. -/


-- @@ L822-822 verbatim
section SweepGen


-- @@ L824-826 verbatim
variable (stE : (Univ A R (P) dt.KIx dt.dd →
    Prop) → TapeSt dt A R (P) I →
  (dt.CtlIx → A) → TapeSt dt A R (P) I)

-- @@ L827-829 verbatim
variable (fsE : (Univ A R (P) dt.KIx dt.dd →
    Prop) → TapeSt dt A R (P) I →
  (dt.CtlIx → A) → dt.CtlIx → A)

-- @@ L830-830 verbatim
variable (hlin : IsLinOrd (WMLe (A := Univ A R (P) dt.KIx dt.dd)))

-- @@ L831-831 verbatim
variable (st₀ : TapeSt dt A R (P) I)

-- @@ L832-832 verbatim
variable (f₀ : dt.CtlIx → A)


-- @@ L834-844 verbatim
/-- **The pair the sweep arrives at each address with**: the base at the
empty address, and at every increment the previous address's evaluation
exit – its marker moved on and its mirror set to the new address, exactly
the shape `DescriptiveComplexity.Draw.Data.reaches_sweep` demands. -/
noncomputable def ixSweepPairG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (P) I × (dt.CtlIx → A) :=
  addrIter (isLinOrd_wmSetLe hlin) (st₀, f₀)
    (fun u p =>
      ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
        fsE u p.1 p.2)) w


-- @@ L846-850 verbatim
/-- The sweep's tape family – `reaches_sweep`'s `SW`. -/
noncomputable def ixSweepSWG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (P) I :=
  (dt.ixSweepPairG (elt := elt) stE fsE hlin st₀ f₀ w).1


-- @@ L852-856 verbatim
/-- The sweep's control family – `reaches_sweep`'s `FS`. -/
noncomputable def ixSweepFSG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    dt.CtlIx → A :=
  (dt.ixSweepPairG (elt := elt) stE fsE hlin st₀ f₀ w).2


-- @@ L858-864 verbatim
/-- The state the sweep leaves each address in – `reaches_sweep`'s
`stE`. -/
noncomputable def ixSweepStEG
    (w : Univ A R (P) dt.KIx dt.dd → Prop) :
    TapeSt dt A R (P) I :=
  stE w (dt.ixSweepSWG (elt := elt)
    stE fsE hlin st₀ f₀ w) (dt.ixSweepFSG (elt := elt) stE fsE hlin st₀ f₀ w)


-- @@ L866-871 verbatim
omit [Finite I] [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
theorem ixSweepSWG_bot :
    dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ (fun _ => False) = st₀ :=
  congrArg Prod.fst (addrIter_bot hlin (isLinOrd_wmSetLe hlin) (st₀, f₀) _)


-- @@ L873-890 verbatim
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R]
  [LinearOrder (P)] [Nonempty A]
  [L.IsRelational] [L.Structure A] in
omit [Finite I] in
/-- **The tape's cover equation** – `reaches_sweep`'s `hSW`, verbatim. -/
theorem ixSweepSWG_incr
    {w w' : Univ A R (P) dt.KIx dt.dd → Prop}
    (hi : WMIncr WMLe w w') :
    dt.ixSweepSWG (elt := elt) stE fsE hlin st₀ f₀ w' =
      { dt.atSt (dt.ixSweepStEG (elt := elt)
        stE fsE hlin st₀ f₀ w) w' with mir := ixMark elt w' } := by
  have h := congrArg Prod.fst
    (addrIter_incr hlin (isLinOrd_wmSetLe hlin) hi (st₀, f₀)
      (fun u p =>
        ({ dt.atSt (stE u p.1 p.2) (wmNext hlin u) with mir := ixMark elt (wmNext hlin u) },
          fsE u p.1 p.2)))
  rw [wmNext_eq hlin hi] at h
  exact h


-- @@ L892-892 verbatim
end SweepGen


-- @@ L894-894 verbatim
/-! ### The sweep's families -/


-- @@ L896-908 verbatim
/-! ### The stage atom's restore, as an algebra

`DescriptiveComplexity.Draw.Data.stageEndSt st v = { st with sav := v,
tgt := v }`: the random access **writes** the home address into SAV and
TARGET whatever they held, so a stage atom is transparent exactly when they
held it already – which is what `ixStageEndSt_eq`'s two hypotheses say, and
why they are not a proof artifact.

Closing the sweep's gap by “reading the mirror” therefore means *threading*
that normalization rather than assuming it away: an atom's exit state is
`ixStageEndSt st v`, and the layers above carry it. These are the equations
that threading needs; they are all definitional, which is what makes the
propagation mechanical. -/


-- @@ L910-910 verbatim
section StageEnd


-- @@ L912-912 verbatim
variable {v : Univ A R (P) dt.KIx dt.dd → Prop}

-- @@ L913-913 verbatim
variable (st : TapeStD dt A R (P))


-- @@ L915-915 verbatim
end StageEnd


-- @@ L917-917 verbatim
end Data


-- @@ L919-919 verbatim
end Draw


-- @@ L921-921 verbatim
end DescriptiveComplexity
