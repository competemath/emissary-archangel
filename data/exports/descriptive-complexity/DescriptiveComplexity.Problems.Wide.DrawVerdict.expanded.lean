/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawRoundSem


-- @@ L8-32 verbatim
/-!
# One variable's verdict *is* one step of the iteration

The capstone `DescriptiveComplexity.Draw.Data.accVerdict_varFM_qfValue`
reads the machinery's exit bit as the alternating prefix over an abstract
leaf `Ps`; `DescriptiveComplexity.Draw.Data.altQuantFrom_leafP` reads that
prefix, at the concrete leaf, as `DescriptiveComplexity.StepDef.next`. This
file joins them, discharging every abstract input of the capstone from the
two facts a reduction's tape maintains:

* the working address's outer blocks encode the argument tuple (`hmb`);
* each stage track holds the stage dictionary (`hdict`).

Two statements: `accVerdict_leafP`, at any variable, whose right-hand side
is the prefix over `DescriptiveComplexity.Draw.Data.leafP` at the
address's blocks – the form the *output* sentence's leg also needs – and
`accVerdict_next`, its specialization at a fixed-point variable, whose
right-hand side is `d.next` itself.

The semantic pack is a *hypothesis* in the form the capstone consumes
(`hsem`, pinning it to `DescriptiveComplexity.Draw.Data.passSem`) rather
than a fixed choice, because the spine's per-position family
(`DescriptiveComplexity.Draw.Data.evalSpine_run`'s `semOfJ`) is chosen by
the caller and only has to *agree* with the pass's pack.
-/


-- @@ L34-34 verbatim
namespace DescriptiveComplexity


-- @@ L36-36 verbatim
namespace Draw


-- @@ L38-38 verbatim
open FirstOrder


-- @@ L40-40 verbatim
open Language Structure


-- @@ L42-42 verbatim
namespace Data


-- @@ L44-44 verbatim
variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}

-- @@ L45-45 verbatim
variable [Fintype dt.SlotIx]

-- @@ L46-46 verbatim
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]

-- @@ L47-47 verbatim
variable [Language.wide.Structure (Univ A R P dt.KIx dt.dd)]

-- @@ L48-48 verbatim
variable [Finite A] [Finite R] [Finite P]

-- @@ L49-49 verbatim
variable {PR : Prog A R P dt.CtlIx dt.SlotIx dt.KIx dt.dd}

-- @@ L50-50 verbatim
variable (RF : RegFile (Univ A R P dt.KIx dt.dd))

-- @@ L51-51 verbatim
variable [Nonempty A] [L.IsRelational] [L.Structure A]

-- @@ L52-52 verbatim
variable [Finite dt.KIx] [LinearOrder (dt.X.Map A)]


-- @@ L54-54 verbatim
section Verdict


-- @@ L56-56 verbatim
variable (vi : dt.VarIx) (st : TapeStD dt A R P)

-- @@ L57-57 verbatim
variable {v : Univ A R P dt.KIx dt.dd → Prop}

-- @@ L58-58 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L59-59 verbatim
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)


-- @@ L61-66 verbatim
/-- **The working address's outer blocks**, as the valuation the free levels
of a pack read: the mirror's block at each outer index. -/
noncomputable def mirBlk : Fin dt.ko → (Fin dt.dd → A) → Prop := fun k =>
  wmBlk st.mir
    (Tag.arg (toLex (Sum.inl k : Fin dt.ko ⊕ Fin dt.ki)) :
      Tag R P dt.KIx)


-- @@ L68-79 verbatim
variable {dt} in
omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx]
  [LinearOrder (dt.X.Map A)] in
/-- The address's blocks depend on the mirror alone. -/
theorem mirBlk_of_mir {st st' : TapeStD dt A R P} (h : st.mir = st'.mir) :
    dt.mirBlk st = dt.mirBlk st' :=
  funext fun k => congrArg
    (fun s => wmBlk s
      (Tag.arg (toLex (Sum.inl k : Fin dt.ko ⊕ Fin dt.ki)) :
        Tag R P dt.KIx)) h


-- @@ L81-85 verbatim
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn vi),
    dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf vi),
    dt.KindSem PR.zero PR.one vi (dt.roundSt st (mV a)) (dt.kindOf vi b))


-- @@ L87-168 verbatim
omit [Finite dt.KIx] in
/-- **The machinery's verdict is the prefix over the leaf**: every abstract
input of `DescriptiveComplexity.Draw.Data.accVerdict_varFM_qfValue`
discharged – the flags by
`DescriptiveComplexity.Draw.Data.ctlBit_roundFX_pass_iff`, the pass by
`DescriptiveComplexity.Draw.Data.roundPass_of_polarities`, the valuation
and its pack by `DescriptiveComplexity.Draw.Data.passW`, the stage reads
by `DescriptiveComplexity.Draw.Data.old_trackOf_stageTgtD`, and the two
leaf readings by `DescriptiveComplexity.Draw.Data.leafP_pass_iff` /
`DescriptiveComplexity.Draw.Data.leafP_fail_iff`. -/
theorem accVerdict_leafP
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mbW : Fin (dt.arOf vi) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf vi),
      dt.mirBlk st (Fin.castLE (dt.arOf_le_ko vi) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (s : Univ A R P dt.KIx dt.dd → Prop), Below s →
      (st.old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf vi)),
      Below (dt.stageTgtD PR.zero vi iv ts (dt.roundSt st (mV a)) v
        (dt.d.B.arity iv)))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn vi),
        dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf vi)),
      semOf a hp b = dt.passSem RF PR.zero_ne_one hlin vi
        (dt.roundSt st (mV a)) hp mbW (fun ℓ => hmb ℓ) b)
    (fG : dt.CtlIx → A) :
    dt.accVerdict PR.one (dt.polOf vi)
      ((dt.varArgsOf PR.zero PR.one vi).postFold
        (dt.roundFX RF hord vi st v mV semOf (dt.varFM RF hord vi st v mV semOf fG aT) aT)
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)) ↔
      altQuantFrom (dt.polOf vi)
        (dt.leafP PR.zero PR.one vi σ (dt.mirBlk st)) 0
        (ixBlk (argIn dt.ko) (mV aT)) := by
  classical
  refine dt.accVerdict_varFM_qfValue (vi := vi) (st := st) (mV := mV)
    (semOf := semOf) (hlin := hlin) (hord := hord) (hbotV := hbotV)
    (hmV0 := hmV0) (hIncr := hIncr) (hKin := hKin) (hTop := hTop) (σ := σ)
    (wOf := fun a hp => dt.passW RF PR.zero PR.one PR.zero_ne_one hlin vi
      (dt.roundSt st (mV a)) hp mbW)
    (hENC := fun a hp j => dt.passW_hENC RF PR.zero_ne_one hlin vi
      (dt.roundSt st (mV a)) hp mbW (fun ℓ => hmb ℓ) j)
    (hOld := fun a hp iv ts => dt.old_trackOf_stageTgtD PR.zero_ne_one vi iv
      (dt.arOf_le_ko (some iv)) σ (dt.roundSt st (mV a)) v (hdict iv) ts
      (fun ℓ => dt.passW_hENC RF PR.zero_ne_one hlin vi
        (dt.roundSt st (mV a)) hp mbW (fun ℓ' => hmb ℓ') (ts ℓ))
      (hbelow a iv ts))
    RF hordP (Ps := dt.leafP PR.zero PR.one vi σ (dt.mirBlk st)) hsem fG
    (Ex := fun a => ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.existGateC →
      dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
    (Al := fun a => ∀ ℓ : Fin (dt.nIn vi), dt.igFlag vi ℓ = dt.allGateC →
      dt.igPassP RF PR.zero PR.one vi (dt.roundSt st (mV a)) ℓ)
    (fun a => dt.ctlBit_roundFX_pass_iff RF hord PR.zero_ne_one (Or.inl rfl) v fG a)
    (fun a => dt.ctlBit_roundFX_pass_iff RF hord PR.zero_ne_one (Or.inr rfl) v fG a)
    (fun _ hE hA => dt.roundPass_of_polarities RF hE hA) ?_ ?_
  · -- a passing round: the leaf is the matrix at the pass's points
    intro a hp
    have hpass := dt.leafP_pass_iff RF PR.zero_ne_one hlin vi
      (dt.roundSt st (mV a)) σ (dt.mirBlk st) mbW (fun ℓ => hmb ℓ) hp
    constructor
    · rintro ⟨-, h2⟩
      exact hpass.mpr (h2 (fun ℓ _ => hp ℓ))
    · intro h
      exact ⟨fun ℓ _ => hp ℓ, fun _ => hpass.mp h⟩
  · -- a failing round: the leaf is the ∃-clause alone
    intro a hEA
    exact dt.leafP_fail_iff RF PR.zero_ne_one hlin vi (dt.roundSt st (mV a)) σ
      (dt.mirBlk st) mbW (fun ℓ => hmb ℓ) hEA


-- @@ L170-170 verbatim
end Verdict


-- @@ L172-172 verbatim
section VerdictNext


-- @@ L174-174 verbatim
variable (st : TapeStD dt A R P)

-- @@ L175-175 verbatim
variable {v : Univ A R P dt.KIx dt.dd → Prop}

-- @@ L176-176 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L177-177 verbatim
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)

-- @@ L178-178 verbatim
variable (i : dt.d.B.ι)

-- @@ L179-184 verbatim
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn (some i)),
    dt.igPassP RF PR.zero PR.one (some i) (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (some i)),
    dt.KindSem PR.zero PR.one (some i) (dt.roundSt st (mV a))
      (dt.kindOf (some i) b))


-- @@ L186-231 verbatim
omit [Finite dt.KIx] in
/-- **The machinery's verdict at a fixed-point variable is one step of the
iteration** at the points the working address's outer blocks encode: the
prefix of `DescriptiveComplexity.Draw.Data.accVerdict_leafP` read through
`DescriptiveComplexity.Draw.Data.altQuantFrom_leafP`. -/
theorem accVerdict_next
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    (mbW : Fin (dt.arOf (some i)) → dt.X.Map A)
    (hmb : ∀ ℓ : Fin (dt.arOf (some i)),
      dt.mirBlk st (Fin.castLE (dt.arOf_le_ko (some i)) ℓ) =
        encMap dt.ly PR.zero PR.one (mbW ℓ))
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (s : Univ A R P dt.KIx dt.dd → Prop), Below s →
      (st.old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (some i))),
      Below (dt.stageTgtD PR.zero (some i) iv ts (dt.roundSt st (mV a)) v
        (dt.d.B.arity iv)))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (some i)),
        dt.igPassP RF PR.zero PR.one (some i) (dt.roundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf (some i))),
      semOf a hp b = dt.passSem RF PR.zero_ne_one hlin (some i)
        (dt.roundSt st (mV a)) hp mbW (fun ℓ => hmb ℓ) b)
    (fG : dt.CtlIx → A) :
    dt.accVerdict PR.one (dt.polOf (some i))
      ((dt.varArgsOf PR.zero PR.one (some i)).postFold
        (dt.roundFX RF hord (some i) st v mV semOf
          (dt.varFM RF hord (some i) st v mV semOf fG aT) aT)
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)) ↔
      dt.d.next σ i mbW := by
  refine (dt.accVerdict_leafP RF (some i) st mV semOf hlin hord hbotV hmV0
    hIncr hKin hTop σ mbW hmb hdict hbelow hordP hsem fG).trans ?_
  exact altQuantFrom_leafP PR.zero_ne_one i σ (dt.mirBlk st) mbW hmb
    (ixBlk (argIn dt.ko) (mV aT))


-- @@ L233-233 verbatim
end VerdictNext


-- @@ L235-235 verbatim
section VerdictOut


-- @@ L237-237 verbatim
variable (st : TapeStD dt A R P)

-- @@ L238-238 verbatim
variable {v : Univ A R P dt.KIx dt.dd → Prop}

-- @@ L239-239 verbatim
variable {ιV : Type} [LinearOrder ιV] [Finite ιV]

-- @@ L240-240 verbatim
variable (mV : ιV → Univ A R P dt.KIx dt.dd → Prop)

-- @@ L241-246 verbatim
variable (semOf : ∀ a : ιV,
  (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
    dt.igPassP RF PR.zero PR.one none (dt.roundSt st (mV a)) ℓ) →
  ∀ b : Fin (dt.natOf (none : dt.VarIx)),
    dt.KindSem PR.zero PR.one none (dt.roundSt st (mV a))
      (dt.kindOf none b))


-- @@ L248-293 verbatim
omit [Finite dt.KIx] in
/-- **The machinery's verdict at the output variable is the output sentence**
at the stage the tracks hold: the prefix of
`DescriptiveComplexity.Draw.Data.accVerdict_leafP` read through
`DescriptiveComplexity.Draw.Data.altQuantFrom_leafP_out`. The output
variable is nullary, so the working address's outer blocks encode the empty
tuple and there is nothing to ask of them – which is why this is the one
verdict a reduction can take at the *empty* address. -/
theorem accVerdict_out
    (hlin : IsLinOrd (WMLe (A := Univ A R P dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R P dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y)
    {a₀ aT : ιV} (hbotV : ∀ a, a₀ ≤ a) (hmV0 : mV a₀ = fun _ => False)
    (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
      WMIncr WMLe (mV a) (mV a'))
    (hKin : ∀ (a : ιV) (t : Tag R P dt.KIx) (w : Fin dt.dd → A),
      mV a (t, w) → ∃ j : Fin dt.ki, t = argIn dt.ko j)
    (hTop : ∀ u, dt.InnerFull (fun u => tagBlk u.1) (mV aT) u)
    (σ : dt.d.B.Assignment (dt.X.Map A))
    {Below : (Univ A R P dt.KIx dt.dd → Prop) → Prop}
    (hdict : ∀ (iv : dt.d.B.ι) (s : Univ A R P dt.KIx dt.dd → Prop), Below s →
      (st.old iv s ↔
        trackOf dt.ly PR.zero PR.one (dt.arOf_le_ko (some iv)) σ s))
    (hbelow : ∀ (a : ιV) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (none : dt.VarIx))),
      Below (dt.stageTgtD PR.zero none iv ts (dt.roundSt st (mV a)) v
        (dt.d.B.arity iv)))
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly PR.zero PR.one PR.zero_ne_one).le p q)
    (hsem : ∀ (a : ιV)
      (hp : ∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.igPassP RF PR.zero PR.one none (dt.roundSt st (mV a)) ℓ)
      (b : Fin (dt.natOf (none : dt.VarIx))),
      semOf a hp b = dt.passSem RF PR.zero_ne_one hlin none
        (dt.roundSt st (mV a)) hp (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) b)
    (fG : dt.CtlIx → A) :
    dt.accVerdict PR.one (dt.polOf (none : dt.VarIx))
      ((dt.varArgsOf PR.zero PR.one none).postFold
        (dt.roundFX RF hord none st v mV semOf
          (dt.varFM RF hord none st v mV semOf fG aT) aT)
        (dt.back RF.cell PR.zero PR.one dt.dd0Le (dt.roundSt st (mV aT)) v)) ↔
      @Sentence.Realize _ (dt.X.Map A) (dt.d.B.structure₁ σ) dt.d.out := by
  refine (dt.accVerdict_leafP RF none st mV semOf hlin hord hbotV hmV0
    hIncr hKin hTop σ (fun ℓ => ℓ.elim0) (fun ℓ => ℓ.elim0) hdict hbelow
    hordP hsem fG).trans ?_
  exact altQuantFrom_leafP_out PR.zero_ne_one σ (dt.mirBlk st)
    (ixBlk (argIn dt.ko) (mV aT))


-- @@ L295-295 verbatim
end VerdictOut


-- @@ L297-297 verbatim
end Data


-- @@ L299-299 verbatim
end Draw


-- @@ L301-301 verbatim
end DescriptiveComplexity
