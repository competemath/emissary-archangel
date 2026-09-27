/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.K
import LeanPool.Incompleteness.Foundation.Modal.Entailment.Grz


-- @@ L11-11 verbatim
/-! # WellKnown -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal


-- @@ L19-19 verbatim
open Entailment


-- @@ L21-21 verbatim
namespace Hilbert


-- @@ L23-23 verbatim
section «lp_section_1»


-- @@ L25-25 verbatim
open Deduction


-- @@ L27-27 verbatim
variable {H : Hilbert α}

-- @@ L28-28 verbatim
variable [DecidableEq α]



-- @@ L31-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasT (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;


-- @@ L37-39 verbatim
instance [hT : H.HasT] : Entailment.HasAxiomT H where
  T φ :=
    maxm ⟨Axioms.T (.atom hT.p), hT.mem_T, (fun b => if hT.p = b then φ else (.atom b)), by simp⟩


-- @@ L41-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasB (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_B : Axioms.B (.atom p) ∈ H.axioms := by tauto;


-- @@ L47-49 verbatim
instance [hB : H.HasB] : Entailment.HasAxiomB H where
  B φ :=
    maxm ⟨Axioms.B (.atom hB.p), hB.mem_B, (fun b => if hB.p = b then φ else (.atom b)), by simp⟩


-- @@ L51-55 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasD (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;


-- @@ L57-59 verbatim
instance [hD : H.HasD] : Entailment.HasAxiomD H where
  D φ :=
    maxm ⟨Axioms.D (.atom hD.p), hD.mem_D, (fun b => if hD.p = b then φ else (.atom b)), by simp⟩



-- @@ L62-66 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasFour (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;


-- @@ L68-71 verbatim
instance [hFour : H.HasFour] : Entailment.HasAxiomFour H where
  Four φ :=
    maxm ⟨Axioms.Four (.atom hFour.p), hFour.mem_Four,
      (fun b => if hFour.p = b then φ else (.atom b)), by simp⟩



-- @@ L74-78 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasFive (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ H.axioms := by tauto;


-- @@ L80-83 verbatim
instance [hFive : H.HasFive] : Entailment.HasAxiomFive H where
  Five φ :=
    maxm ⟨Axioms.Five (.atom hFive.p), hFive.mem_Five,
      (fun b => if hFive.p = b then φ else (.atom b)), by simp⟩



-- @@ L86-90 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasDot2 (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Dot2 : Axioms.Dot2 (.atom p) ∈ H.axioms := by tauto;


-- @@ L92-95 verbatim
instance [hDot2 : H.HasDot2] : Entailment.HasAxiomDot2 H where
  Dot2 φ :=
    maxm ⟨Axioms.Dot2 (.atom hDot2.p), hDot2.mem_Dot2,
      (fun b => if hDot2.p = b then φ else (.atom b)), by simp⟩



-- @@ L98-105 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasDot3 (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  /-- Imported declaration from the Incompleteness formalization. -/
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Dot3 : Axioms.Dot3 (.atom p) (.atom q) ∈ H.axioms := by tauto;


-- @@ L107-111 verbatim
instance [hDot3 : H.HasDot3] : Entailment.HasAxiomDot3 H where
  Dot3 φ ψ :=
    maxm ⟨Axioms.Dot3 (.atom hDot3.p) (.atom hDot3.q), hDot3.mem_Dot3,
      (fun b => if hDot3.p = b then φ else if hDot3.q = b then ψ else (.atom b)),
      by simp [hDot3.ne_pq]⟩



-- @@ L114-118 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasL (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;


-- @@ L120-122 verbatim
instance [hL : H.HasL] : Entailment.HasAxiomL H where
  L φ :=
    maxm ⟨Axioms.L (.atom hL.p), hL.mem_L, (fun b => if hL.p = b then φ else (.atom b)), by simp⟩



-- @@ L125-129 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasGrz (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ H.axioms := by tauto;


-- @@ L131-134 verbatim
instance [hGrz : H.HasGrz] : Entailment.HasAxiomGrz H where
  Grz φ :=
    maxm ⟨Axioms.Grz (.atom hGrz.p), hGrz.mem_Grz,
      (fun b => if hGrz.p = b then φ else (.atom b)), by simp⟩



-- @@ L137-141 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasTc (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ H.axioms := by tauto;


-- @@ L143-146 verbatim
instance [hTc : H.HasTc] : Entailment.HasAxiomTc H where
  Tc φ :=
    maxm ⟨Axioms.Tc (.atom hTc.p), hTc.mem_Tc,
      (fun b => if hTc.p = b then φ else (.atom b)), by simp⟩



-- @@ L149-153 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasVer (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ H.axioms := by tauto;


-- @@ L155-158 verbatim
instance [hVer : H.HasVer] : Entailment.HasAxiomVer H where
  Ver φ :=
    maxm ⟨Axioms.Ver (.atom hVer.p), hVer.mem_Ver,
      (fun b => if hVer.p = b then φ else (.atom b)), by simp⟩



-- @@ L161-165 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HasH (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_H : Axioms.H (.atom p) ∈ H.axioms := by tauto;


-- @@ L167-169 verbatim
instance [hH : H.HasH] : Entailment.HasAxiomH H where
  H φ :=
    maxm ⟨Axioms.H (.atom hH.p), hH.mem_H, (fun b => if hH.p = b then φ else (.atom b)), by simp⟩


-- @@ L171-171 verbatim
end «lp_section_1»


-- @@ L173-174 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KT : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩

-- @@ L175-175 verbatim
instance : (Hilbert.KT).HasK where p := 0; q := 1;

-- @@ L176-176 verbatim
instance : (Hilbert.KT).HasT where p := 0

-- @@ L177-177 verbatim
instance : Entailment.KT (Hilbert.KT) where



-- @@ L180-181 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}⟩

-- @@ L182-182 verbatim
instance : (Hilbert.KD).HasK where p := 0; q := 1;

-- @@ L183-183 verbatim
instance : (Hilbert.KD).HasD where p := 0

-- @@ L184-184 verbatim
instance : Entailment.KD (Hilbert.KD) where



-- @@ L187-188 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}⟩

-- @@ L189-189 verbatim
instance : (Hilbert.KB).HasK where p := 0; q := 1;

-- @@ L190-190 verbatim
instance : (Hilbert.KB).HasB where p := 0

-- @@ L191-191 verbatim
instance : Entailment.KB (Hilbert.KB) where



-- @@ L194-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KDB : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}⟩

-- @@ L197-197 verbatim
instance : (Hilbert.KDB).HasK where p := 0; q := 1;

-- @@ L198-198 verbatim
instance : (Hilbert.KDB).HasD where p := 0

-- @@ L199-199 verbatim
instance : (Hilbert.KDB).HasB where p := 0

-- @@ L200-200 verbatim
instance : Entailment.KDB (Hilbert.KDB) where



-- @@ L203-205 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KTB : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}⟩

-- @@ L206-206 verbatim
instance : (Hilbert.KTB).HasK where p := 0; q := 1;

-- @@ L207-207 verbatim
instance : (Hilbert.KTB).HasT where p := 0

-- @@ L208-208 verbatim
instance : (Hilbert.KTB).HasB where p := 0

-- @@ L209-209 verbatim
instance : Entailment.KTB (Hilbert.KTB) where



-- @@ L212-213 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩

-- @@ L214-214 verbatim
instance : (Hilbert.K4).HasK where p := 0; q := 1;

-- @@ L215-215 verbatim
instance : (Hilbert.K4).HasFour where p := 0

-- @@ L216-216 verbatim
instance : Entailment.K4 (Hilbert.K4) where



-- @@ L219-221 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KT4B : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}⟩

-- @@ L222-222 verbatim
instance : (Hilbert.KT4B).HasK where p := 0; q := 1;

-- @@ L223-223 verbatim
instance : (Hilbert.KT4B).HasT where p := 0

-- @@ L224-224 verbatim
instance : (Hilbert.KT4B).HasFour where p := 0



-- @@ L227-229 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K45 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩

-- @@ L230-230 verbatim
instance : (Hilbert.K45).HasK where p := 0; q := 1;

-- @@ L231-231 verbatim
instance : (Hilbert.K45).HasFour where p := 0

-- @@ L232-232 verbatim
instance : (Hilbert.K45).HasFive where p := 0

-- @@ L233-233 verbatim
instance : Entailment.K45 (Hilbert.K45) where



-- @@ L236-238 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD4 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}⟩

-- @@ L239-239 verbatim
instance : (Hilbert.KD4).HasK where p := 0; q := 1;

-- @@ L240-240 verbatim
instance : (Hilbert.KD4).HasD where p := 0

-- @@ L241-241 verbatim
instance : (Hilbert.KD4).HasFour where p := 0

-- @@ L242-242 verbatim
instance : Entailment.KD4 (Hilbert.KD4) where



-- @@ L245-247 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD5 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}⟩

-- @@ L248-248 verbatim
instance : (Hilbert.KD5).HasK where p := 0; q := 1;

-- @@ L249-249 verbatim
instance : (Hilbert.KD5).HasD where p := 0

-- @@ L250-250 verbatim
instance : (Hilbert.KD5).HasFive where p := 0

-- @@ L251-251 verbatim
instance : Entailment.KD5 (Hilbert.KD5) where



-- @@ L254-256 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD45 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩

-- @@ L257-257 verbatim
instance : (Hilbert.KD45).HasK where p := 0; q := 1;

-- @@ L258-258 verbatim
instance : (Hilbert.KD45).HasD where p := 0

-- @@ L259-259 verbatim
instance : (Hilbert.KD45).HasFour where p := 0

-- @@ L260-260 verbatim
instance : (Hilbert.KD45).HasFive where p := 0

-- @@ L261-261 verbatim
instance : Entailment.KD45 (Hilbert.KD45) where



-- @@ L264-266 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB4 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}⟩

-- @@ L267-267 verbatim
instance : (Hilbert.KB4).HasK where p := 0; q := 1;

-- @@ L268-268 verbatim
instance : (Hilbert.KB4).HasB where p := 0

-- @@ L269-269 verbatim
instance : (Hilbert.KB4).HasFour where p := 0

-- @@ L270-270 verbatim
instance : Entailment.KB4 (Hilbert.KB4) where



-- @@ L273-275 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB5 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}⟩

-- @@ L276-276 verbatim
instance : (Hilbert.KB5).HasK where p := 0; q := 1;

-- @@ L277-277 verbatim
instance : (Hilbert.KB5).HasB where p := 0

-- @@ L278-278 verbatim
instance : (Hilbert.KB5).HasFive where p := 0

-- @@ L279-279 verbatim
instance : Entailment.KB5 (Hilbert.KB5) where



-- @@ L282-284 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩

-- @@ L285-285 verbatim
instance : (Hilbert.S4).HasK where p := 0; q := 1;

-- @@ L286-286 verbatim
instance : (Hilbert.S4).HasT where p := 0

-- @@ L287-287 verbatim
instance : (Hilbert.S4).HasFour where p := 0

-- @@ L288-288 verbatim
instance : Entailment.S4 (Hilbert.S4) where


-- @@ L290-290 expanded
lemma K4_weakerThan_S4 : WeakerThan Hilbert.K4 Hilbert.S4 :=
  weakerThan_of_dominate_axioms <| by simp;


-- @@ L292-294 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot2 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dot2 (.atom 0)}⟩

-- @@ L295-295 verbatim
instance : (Hilbert.S4Dot2).HasK where p := 0; q := 1;

-- @@ L296-296 verbatim
instance : (Hilbert.S4Dot2).HasT where p := 0

-- @@ L297-297 verbatim
instance : (Hilbert.S4Dot2).HasFour where p := 0

-- @@ L298-298 verbatim
instance : (Hilbert.S4Dot2).HasDot2 where p := 0

-- @@ L299-299 verbatim
instance : Entailment.S4Dot2 (Hilbert.S4Dot2) where



-- @@ L302-305 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot3 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0),
    Axioms.Dot3 (.atom 0) (.atom 1)}⟩

-- @@ L306-306 verbatim
instance : (Hilbert.S4Dot3).HasK where p := 0; q := 1;

-- @@ L307-307 verbatim
instance : (Hilbert.S4Dot3).HasT where p := 0

-- @@ L308-308 verbatim
instance : (Hilbert.S4Dot3).HasFour where p := 0

-- @@ L309-309 verbatim
instance : (Hilbert.S4Dot3).HasDot3 where p := 0; q := 1;

-- @@ L310-310 verbatim
instance : Entailment.S4Dot3 (Hilbert.S4Dot3) where



-- @@ L313-314 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}⟩

-- @@ L315-315 verbatim
instance : (Hilbert.K5).HasK where p := 0; q := 1;

-- @@ L316-316 verbatim
instance : (Hilbert.K5).HasFive where p := 0

-- @@ L317-317 verbatim
instance : Entailment.K5 (Hilbert.K5) where



-- @@ L320-322 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5 : Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩

-- @@ L323-323 verbatim
instance : (Hilbert.S5).HasK where p := 0; q := 1;

-- @@ L324-324 verbatim
instance : (Hilbert.S5).HasT where p := 0

-- @@ L325-325 verbatim
instance : (Hilbert.S5).HasFive where p := 0

-- @@ L326-326 verbatim
instance : Entailment.S5 (Hilbert.S5) where



-- @@ L329-330 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩

-- @@ L331-331 verbatim
instance : (Hilbert.GL).HasK where p := 0; q := 1;

-- @@ L332-332 verbatim
instance : (Hilbert.GL).HasL where p := 0

-- @@ L333-333 verbatim
instance : Entailment.GL (Hilbert.GL) where


-- @@ L335-336 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KH : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.H (.atom 0)}⟩

-- @@ L337-337 verbatim
instance : (Hilbert.KH).HasK where p := 0; q := 1;

-- @@ L338-338 verbatim
instance : (Hilbert.KH).HasH where p := 0


-- @@ L340-341 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩

-- @@ L342-342 verbatim
instance : (Hilbert.Grz).HasK where p := 0; q := 1;

-- @@ L343-343 verbatim
instance : (Hilbert.Grz).HasGrz where p := 0

-- @@ L344-344 verbatim
instance : Entailment.Grz (Hilbert.Grz) where


-- @@ L346-346 expanded
lemma KT_weakerThan_Grz : WeakerThan Hilbert.KT Hilbert.Grz :=
  weakerThan_of_dominate_axioms <| by simp;


-- @@ L349-350 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩

-- @@ L351-351 verbatim
instance : (Hilbert.Ver).HasK where p := 0; q := 1;

-- @@ L352-352 verbatim
instance : (Hilbert.Ver).HasVer where p := 0

-- @@ L353-353 verbatim
instance : Entailment.Ver (Hilbert.Ver) where



-- @@ L356-358 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Triv : Hilbert ℕ :=
  ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩

-- @@ L359-359 verbatim
instance : (Hilbert.Triv).HasK where p := 0; q := 1;

-- @@ L360-360 verbatim
instance : (Hilbert.Triv).HasT where p := 0

-- @@ L361-361 verbatim
instance : (Hilbert.Triv).HasTc where p := 0

-- @@ L362-362 verbatim
instance : Entailment.Triv (Hilbert.Triv) where


-- @@ L364-364 expanded
lemma K4_weakerThan_Triv : WeakerThan Hilbert.K4 Hilbert.Triv :=
  weakerThan_of_dominate_axioms <| by simp;


-- @@ L366-367 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev N : Hilbert ℕ := ⟨{}⟩


-- @@ L369-369 verbatim
end Hilbert


-- @@ L371-371 verbatim
end Modal

-- @@ L372-372 verbatim
end LO
