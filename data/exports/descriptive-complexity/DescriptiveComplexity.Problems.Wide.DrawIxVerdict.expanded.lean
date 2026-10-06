/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxRoundSem
import DescriptiveComplexity.Problems.Wide.DrawVerdict


-- @@ L9-15 verbatim
/-!
# One variable's verdict at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawVerdict` read at a coarse file: the
machinery's exit bit as the alternating prefix over the leaf, and its
specialization at a fixed-point variable and at the output.
-/


-- @@ L17-17 verbatim
namespace DescriptiveComplexity


-- @@ L19-19 verbatim
namespace Draw


-- @@ L21-21 verbatim
open FirstOrder


-- @@ L23-23 verbatim
open Language Structure


-- @@ L25-25 verbatim
namespace Data


-- @@ L27-27 verbatim
variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}

-- @@ L28-28 verbatim
variable [Fintype dt.SlotIx]

-- @@ L29-29 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]

-- @@ L30-30 verbatim
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]

-- @@ L31-31 verbatim
variable [Finite A] [Finite R] [Finite P]

-- @@ L32-32 verbatim
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}

-- @@ L33-33 verbatim
variable {I : Type} [Finite I] (F : LaidFile dt A R P I)

-- @@ L34-34 verbatim
variable {elt : I → Univ A R P dt.KIx dt.dd}

-- @@ L35-35 verbatim
variable (hinj : Function.Injective elt)

-- @@ L36-36 verbatim
variable (hhasP : F.toLayout.HasName PR.zero)

-- @@ L37-38 verbatim
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))

-- @@ L39-39 verbatim
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)

-- @@ L40-40 verbatim
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)

-- @@ L41-41 verbatim
variable {Use : I → Prop}

-- @@ L42-42 verbatim
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))

-- @@ L43-44 verbatim
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd), Use u →
  WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)

-- @@ L45-46 verbatim
variable [Nonempty A] [L.IsRelational] [L.Structure A]
-- The marks-to-shapes bridge at a coarse file (see `DrawIxRoundSem`).

-- @@ L47-51 verbatim
variable (hpassEnc : ∀ (vi : dt.VarIx) (stV : TapeSt dt A R P I)
    (ℓ : Fin (dt.nIn vi)),
  dt.ixIGPassP (elt := elt) F PR.zero PR.one vi stV ℓ ↔
    IsEnc dt.ly PR.zero PR.one (wmBlk (ixAddr elt stV.val)
      (Tag.arg (toLex (dt.igBlk vi ℓ)) : Tag R P dt.KIx)))

-- @@ L52-52 verbatim
variable [Finite dt.KIx] [LinearOrder (dt.X.Map A)]


-- @@ L54-54 verbatim
section Verdict


-- @@ L56-56 verbatim
variable (vi : dt.VarIx) (st : TapeSt dt A R P I)

-- @@ L57-57 verbatim
variable {v : Univ A R P dt.KIx dt.dd → Prop}

-- @@ L58-58 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L59-59 verbatim
variable (mV : ιV → I → Prop)


-- @@ L61-66 verbatim
/-- **The working address's outer blocks**, as the valuation the free levels
of a pack read: the mirror's block at each outer index. -/
noncomputable def ixMirBlk : Fin dt.ko → (Fin dt.dd → A) → Prop := fun k =>
  wmBlk (ixAddr elt st.mir)
    (Tag.arg (toLex (Sum.inl k : Fin dt.ko ⊕ Fin dt.ki)) :
      Tag R P dt.KIx)


-- @@ L68-80 verbatim
variable {dt} in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] in
omit [Finite I] in
/-- The address's blocks depend on the mirror alone. -/
theorem ixMirBlk_of_mir {st st' : TapeSt dt A R P I} (h : st.mir = st'.mir) :
    dt.ixMirBlk (elt := elt) st = dt.ixMirBlk (elt := elt) st' :=
  funext fun k => congrArg
    (fun s => wmBlk (ixAddr elt s)
      (Tag.arg (toLex (Sum.inl k : Fin dt.ko ⊕ Fin dt.ki)) :
        Tag R P dt.KIx)) h


-- @@ L82-86 verbatim
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.IxKindSem PR.zero PR.one vi (dt.ixRoundSt st (mV a)) elt (dt.kindOf vi b))


-- @@ L88-197 verbatim
omit [Finite I] [Finite dt.KIx] in
include hinj hhasP heltP hix hblkP hmono hup hpassEnc in
/-- **The machinery's verdict is the prefix over the leaf**: every abstract
input of `DescriptiveComplexity.Draw.Data.ixAccVerdict_varFM_qfValue`
discharged – the flags by
`DescriptiveComplexity.Draw.Data.ixCtlBit_roundFX_pass_iff`, the pass by
`DescriptiveComplexity.Draw.Data.ixRoundPass_of_polarities`, the valuation
and its pack by `DescriptiveComplexity.Draw.Data.ixPassW`, the stage reads
by `DescriptiveComplexity.Draw.Data.ixOld_stage_of_dict`, and the two
leaf readings by `DescriptiveComplexity.Draw.Data.ixLeafP_pass_iff` /
`DescriptiveComplexity.Draw.Data.ixLeafP_fail_iff`. -/
theorem ixAccVerdict_leafP
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      dt.ixMirBlk (elt := elt) st (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi)),
      Below (ixAddr elt (dt.ixStageTgt F hhasP vi ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v } (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf vi)),
      semOf a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc)
        (vi := vi) (stV := dt.ixRoundSt st (mV a)) (hp := hp) (mbW := mbW)
        (hmb := fun ℓ => hmb ℓ) b)
    (fG : dt.CtlIx → A) :
    dt.accVerdict PR.one (dt.polOf vi)
      ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP
          vi st v mV semOf (dt.ixVarFM (elt := elt) F hinj hhasP heltP vi st v mV semOf fG aT) aT)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)) ↔
      altQuantFrom (dt.polOf vi)
        (dt.leafP PR.zero PR.one vi σ (dt.ixMirBlk (elt := elt) st)) 0
        (ixBlk (argIn dt.ko) (ixAddr elt (mV aT))) := by
  classical
  refine dt.ixAccVerdict_varFM_qfValue (F := F) (elt := elt) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (vi := vi) (st := st) (mV := mV)
    (semOf := semOf) (hlin := hlin) (hord := hord) (hbotV := hbotV)
    (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr) (hKin := hKin) (hTop := hTop)
    (σ := σ)
    (wOf := fun a hp => dt.ixPassW (elt := elt) (F := F) (zero := PR.zero)
      (one := PR.one) (hpassEnc := hpassEnc) (vi := vi)
      (stV := dt.ixRoundSt st (mV a)) (hp := hp) (mbW := mbW))
    (hENC := fun a hp j => dt.ixPassW_hENC (elt := elt) (F := F)
      (hpassEnc := hpassEnc) (vi := vi) (stV := dt.ixRoundSt st (mV a))
      (hp := hp) (mbW := mbW) (hmb := fun ℓ => hmb ℓ) j)
    (hOld := fun a hp iv ts => ixOld_stage_of_dict (dt := dt) (F := F)
      (hhas := hhasP) (helt := heltP) (hinj := hinj)
      (vi := vi) (iv := iv) (ha := dt.arOf_le_ko (some iv)) (σ := σ)
      (stV := { dt.ixRoundSt st (mV a) with sav := ixMark elt v })
      (hdict := hdict iv) (ts := ts)
      (hsrc := fun ℓ => dt.ixPassW_hENC (elt := elt) (F := F)
        (hpassEnc := hpassEnc) (vi := vi) (stV := dt.ixRoundSt st (mV a))
        (hp := hp) (mbW := mbW) (hmb := fun ℓ' => hmb ℓ') (ts ℓ))
      (hbelow := hbelow a iv ts))
    (hordP := hordP) (Ps := dt.leafP PR.zero PR.one vi σ
      (dt.ixMirBlk (elt := elt) st)) (hsem := hsem) (fG := fG)
    (Ex := fun a => ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
      dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
    (Al := fun a => ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.allGateC →
      dt.ixIGPassP (elt := elt) F PR.zero PR.one vi (dt.ixRoundSt st (mV a)) ℓ)
    (hEx := fun a => ixCtlBit_roundFX_pass_iff (dt := dt) (elt := elt) (F := F)
      (hinj := hinj) (hhasP := hhasP) (heltP := heltP) (vi := vi) (st := st)
      (mV := mV) (semOf := semOf) (hzo := PR.zero_ne_one) (hq := Or.inl rfl)
      (v := v) (fG := fG) (a := a))
    (hAll := fun a => ixCtlBit_roundFX_pass_iff (dt := dt) (elt := elt) (F := F)
      (hinj := hinj) (hhasP := hhasP) (heltP := heltP) (vi := vi) (st := st)
      (mV := mV) (semOf := semOf) (hzo := PR.zero_ne_one) (hq := Or.inr rfl)
      (v := v) (fG := fG) (a := a))
    (hPass := fun _ hE hA => ixRoundPass_of_polarities (dt := dt) (elt := elt)
      (F := F) (vi := vi) (zero := PR.zero) (one := PR.one)
      (hEx := hE) (hAl := hA)) ?_ ?_
  · -- a passing round: the leaf is the matrix at the pass's points
    intro a hp
    have hpass := ixLeafP_pass_iff (dt := dt) (elt := elt) (F := F)
      (hpassEnc := hpassEnc) (hzo := PR.zero_ne_one) (vi := vi)
      (stV := dt.ixRoundSt st (mV a)) (σ := σ) (mb := dt.ixMirBlk (elt := elt) st)
      (mbW := mbW) (hmb := fun ℓ => hmb ℓ) (hp := hp)
    constructor
    · rintro ⟨-, h2⟩
      exact hpass.mpr (h2 (fun ℓ _ => hp ℓ))
    · intro h
      exact ⟨fun ℓ _ => hp ℓ, fun _ => hpass.mp h⟩
  · -- a failing round: the leaf is the ∃-clause alone
    intro a hEA
    exact ixLeafP_fail_iff (dt := dt) (elt := elt) (F := F) (hpassEnc := hpassEnc)
      (vi := vi) (stV := dt.ixRoundSt st (mV a)) (σ := σ)
      (mb := dt.ixMirBlk (elt := elt) st) (mbW := mbW) (hmb := fun ℓ => hmb ℓ)
      (hEA := hEA)


-- @@ L199-199 verbatim
end Verdict


-- @@ L201-201 verbatim
section VerdictNext


-- @@ L203-203 verbatim
variable (st : TapeSt dt A R P I)

-- @@ L204-204 verbatim
variable {v : Univ A R P dt.KIx dt.dd → Prop}

-- @@ L205-205 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L206-206 verbatim
variable (mV : ιV → I → Prop)

-- @@ L207-207 verbatim
variable (i : dt.d.B.ι)

-- @@ L208-213 verbatim
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn (some i)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one (some i) (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (some i)),
    dt.IxKindSem PR.zero PR.one (some i) (dt.ixRoundSt st (mV a))
      elt (dt.kindOf (some i) b))


-- @@ L215-271 verbatim
omit [Finite I] [Finite dt.KIx] in
include hinj hhasP heltP hix hblkP hmono hup hpassEnc in
/-- **The machinery's verdict at a fixed-point variable is one step of the
iteration** at the points the working address's outer blocks encode: the
prefix of `DescriptiveComplexity.Draw.Data.ixAccVerdict_leafP` read through
`DescriptiveComplexity.Draw.Data.altQuantFrom_leafP`. -/
theorem ixAccVerdict_next
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mbW : Fin (dt.arOf (some i)) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf (some i)),
      dt.ixMirBlk (elt := elt) st (Fin.castLE (dt.arOf_le_ko (some i)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (some i))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP (some i) ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v } (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (some i)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (some i) (dt.ixRoundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf (some i))),
      semOf a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc)
        (vi := some i) (stV := dt.ixRoundSt st (mV a)) (hp := hp) (mbW := mbW)
        (hmb := fun ℓ => hmb ℓ) b)
    (fG : dt.CtlIx → A) :
    dt.accVerdict PR.one (dt.polOf (some i))
      ((dt.varArgsOf PR.zero PR.one (some i)).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP (some i) st v mV semOf
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP (some i) st v mV semOf fG aT) aT)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)) ↔
      dt.d.next σ i mbW := by
  refine (ixAccVerdict_leafP (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc) (vi := some i)
    (st := st) (mV := mV) (semOf := semOf) (hlin := hlin) (hord := hord)
    (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr)
    (hKin := hKin) (hTop := hTop) (σ := σ) (mbW := mbW) (hmb := hmb)
    (hdict := hdict) (hbelow := hbelow) (hordP := hordP) (hsem := hsem)
    (fG := fG)).trans ?_
  exact altQuantFrom_leafP PR.zero_ne_one i σ (dt.ixMirBlk (elt := elt) st) mbW hmb
    (ixBlk (argIn dt.ko) (ixAddr elt (mV aT)))


-- @@ L273-273 verbatim
end VerdictNext


-- @@ L275-275 verbatim
section VerdictOut


-- @@ L277-277 verbatim
variable (st : TapeSt dt A R P I)

-- @@ L278-278 verbatim
variable {v : Univ A R P dt.KIx dt.dd → Prop}

-- @@ L279-279 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L280-280 verbatim
variable (mV : ιV → I → Prop)

-- @@ L281-286 verbatim
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
    dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixRoundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (none : dt.VarIx)),
    dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt st (mV a))
      elt (dt.kindOf none b))


-- @@ L288-343 verbatim
omit [Finite I] [Finite dt.KIx] in
include hinj hhasP heltP hix hblkP hmono hup hpassEnc in
/-- **The machinery's verdict at the output variable is the output sentence**
at the stage the tracks hold: the prefix of
`DescriptiveComplexity.Draw.Data.ixAccVerdict_leafP` read through
`DescriptiveComplexity.Draw.Data.altQuantFrom_leafP_out`. The output
variable is nullary, so the working address's outer blocks encode the empty
tuple and there is nothing to ask of them – which is why this is the one
verdict a reduction can take at the *empty* address. -/
theorem ixAccVerdict_out
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hUse : ∀ (a : ιV) (u : I), mV a u → Use u)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr F.le (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      ixAddr elt (mV a) (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (ixAddr elt (mV aT)) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      Below (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) →
      (st.old iv (tupAddr dt.ly PR.zero PR.one (R := R) (P := P) (ki := dt.ki)
        (dt.arOf_le_ko (some iv)) x) ↔ σ iv x))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (ixAddr elt (dt.ixStageTgt F hhasP none ts
        { dt.ixRoundSt st (mV a) with sav := ixMark elt v } (dt.d.B.arity iv))))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixRoundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf (none : dt.VarIx))),
      semOf a hp b = dt.ixPassSem (elt := elt) (F := F) (hpassEnc := hpassEnc)
        (vi := none) (stV := dt.ixRoundSt st (mV a)) (hp := hp)
        (mbW := fun ℓ => ℓ.elim0) (hmb := fun ℓ => ℓ.elim0) b)
    (fG : dt.CtlIx → A) :
    dt.accVerdict PR.one (dt.polOf (none : dt.VarIx))
      ((dt.varArgsOf PR.zero PR.one none).postFold
        (dt.ixRoundFX (elt := elt) F hinj hhasP heltP none st v mV semOf
          (dt.ixVarFM (elt := elt) F hinj hhasP heltP none st v mV semOf fG aT) aT)
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)) ↔
      @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out := by
  refine (ixAccVerdict_leafP (dt := dt) (elt := elt) (F := F) (hinj := hinj)
    (hhasP := hhasP) (heltP := heltP) (hix := hix) (hblkP := hblkP)
    (hmono := hmono) (hup := hup) (hpassEnc := hpassEnc) (vi := none)
    (st := st) (mV := mV) (semOf := semOf) (hlin := hlin) (hord := hord)
    (hbotV := hbotV) (hmV0 := hmV0) (hUse := hUse) (hIncr := hIncr)
    (hKin := hKin) (hTop := hTop) (σ := σ) (mbW := fun ℓ => ℓ.elim0)
    (hmb := fun ℓ => ℓ.elim0) (hdict := hdict) (hbelow := hbelow)
    (hordP := hordP) (hsem := hsem) (fG := fG)).trans ?_
  exact altQuantFrom_leafP_out PR.zero_ne_one σ (dt.ixMirBlk (elt := elt) st)
    (ixBlk (argIn dt.ko) (ixAddr elt (mV aT)))


-- @@ L345-345 verbatim
end VerdictOut


-- @@ L347-347 verbatim
end Data


-- @@ L349-349 verbatim
end Draw


-- @@ L351-351 verbatim
end DescriptiveComplexity
