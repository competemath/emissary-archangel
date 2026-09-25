import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Prismriver.Repr.Classical
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Prismriver.Repr.Dihedral

-- @@ L7-7 verbatim
namespace Prismriver.Theory.Dihedral


-- @@ L9-9 verbatim
open Classical

-- @@ L10-10 verbatim
open Lean

-- @@ L11-11 verbatim
open Dihedral


-- @@ L13-14 verbatim
inductive Parity : Type | major | minor
deriving DecidableEq, Repr


-- @@ L16-17 verbatim
instance : ToString Parity where
  toString | .major => "major" | .minor => "minor"


-- @@ L19-21 verbatim
def Parity.flip : Parity → Parity
  | .major => .minor
  | .minor => .major


-- @@ L23-23 verbatim
abbrev Triad := ZMod 12 × Parity


-- @@ L25-26 verbatim
def pitch_toZMod12 (p : Pitch) : ZMod 12 :=
  (p.acc.semitones + nameDistance p.name 0 : Int)


-- @@ L28-29 verbatim
def interval_toZMod12 (i : Interval) : ZMod 12 :=
  (i.semitones : ZMod 12)


-- @@ L31-43 verbatim
def ZMod12ToPitch : ZMod 12 → Pitch
  | 0 => Pitch.new .c 0
  | 1 => Pitch.new .c 0 .sharp
  | 2 => Pitch.new .d 0
  | 3 => Pitch.new .d 0 .sharp
  | 4 => Pitch.new .e 0
  | 5 => Pitch.new .f 0
  | 6 => Pitch.new .f 0 .sharp
  | 7 => Pitch.new .g 0
  | 8 => Pitch.new .g 0 .sharp
  | 9 => Pitch.new .a 0
  | 10 => Pitch.new .a 0 .sharp
  | 11 => Pitch.new .b 0


-- @@ L45-48 verbatim
instance : ToString Triad where
  toString t :=
    let pitch := ZMod12ToPitch t.1
    s!"({pitch}, {t.2})"


-- @@ L50-57 verbatim
def TransposeAction.toDihedral :
      @TransposeAction Pitch Interval → DihedralGroup 12
    | .r i =>
        DihedralGroup.r (interval_toZMod12 i)
    | .sr a i =>
        DihedralGroup.sr (interval_toZMod12 i - 2 * pitch_toZMod12 a)

-- convert triad to list of pitches

-- @@ L58-65 verbatim
def recoverTriple (t : Triad) : List Pitch :=
  match t.2 with
  | .major =>
    let p := ZMod12ToPitch t.1
    p :: major3.map (· • p)
  | .minor =>
    let p := ZMod12ToPitch (t.1 + 5)
    p :: minor3.map (· • p)


-- @@ L67-68 verbatim
def transposeTriad (n : ZMod 12) (t : Triad) : Triad :=
  (t.1 + n, t.2)


-- @@ L70-76 verbatim
def invertTriad (n : ZMod 12) (t : Triad) : Triad :=
    (-t.1 + n, t.2.flip)

-- note: mathlib's dihedral group uses the opposite rotation convention from the paper.
-- The paper's T_n corresponds to Mathlib's r (-n), not r n.
-- paper's s^12=1, t^2=1, tst=s^{-1} vs Mathlib's r * sr = sr (j - i).
-- fix is transposing by -n when the group element is r n.

-- @@ L77-83 verbatim
instance : SMul (DihedralGroup 12) Triad where
  smul g t :=
    match g with
    | DihedralGroup.r n =>
        transposeTriad n t
    | DihedralGroup.sr n =>
        invertTriad (-n) t


-- @@ L85-90 verbatim
lemma transposeTriad_zero (t : Triad) :
    transposeTriad 0 t = t := by
    unfold transposeTriad
    simp

-- Tm ◦ Tn = Tm+n mod 12

-- @@ L91-103 verbatim
lemma transposeTriad_add (i j : ZMod 12) (t : Triad) :
    transposeTriad i (transposeTriad j t) = transposeTriad (i + j) t := by
    unfold transposeTriad
    simp
    rw [add_assoc]
    simp
    rw [add_comm]

-- for all pitch action, there exists dihedral such that action applied to pitch = dihedral applied to pitch
-- = dihedralize a acts on equivalence class of pitch
-- image of an operation

-- Tm ◦ In = Im+n mod 12

-- @@ L104-113 verbatim
lemma transposeInverse_add (i j : ZMod 12) (t : Triad) :
  transposeTriad i (invertTriad j t) = invertTriad (i + j) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [add_assoc]
  simp
  rw [add_comm]

-- Im ◦ Tn = Im−n mod 12

-- @@ L114-124 verbatim
lemma inverseTranspose_subtract (i j : ZMod 12) (t : Triad) :
  invertTriad i (transposeTriad j t) = invertTriad (i - j) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]

-- Im ◦ In = Tm−n mod 12

-- @@ L125-137 verbatim
lemma inverseInverse_subtract (i j : ZMod 12) (t : Triad) :
  invertTriad i (invertTriad j t) = transposeTriad (i - j) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [sub_eq_add_neg]
  constructor
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]
  cases t.2
  rfl
  rfl


-- @@ L139-153 verbatim
lemma inverseInverse_subtract' (i j : ZMod 12) (t : Triad) :
  invertTriad (-i) (invertTriad (-j) t) = transposeTriad (j - i) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [sub_eq_add_neg]
  constructor
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]
  simp
  rw [add_comm]
  cases t.2
  rfl
  rfl


-- @@ L155-183 verbatim
instance : MulAction (DihedralGroup 12) Triad where
    one_smul t := by
      cases t
      simp only [DihedralGroup.one_def]
      apply transposeTriad_zero
    mul_smul t x y := by
      cases t <;> cases x
      · -- r.r
        rw [DihedralGroup.r_mul_r]
        simp only [HSMul.hSMul, SMul.smul]
        symm
        apply transposeTriad_add
      · -- r.sr
        rw [DihedralGroup.r_mul_sr]
        simp only [HSMul.hSMul, SMul.smul]
        simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
        symm
        apply transposeInverse_add
      · -- sr.r
        rw [DihedralGroup.sr_mul_r]
        simp only [HSMul.hSMul, SMul.smul]
        symm
        rw [neg_add']
        apply inverseTranspose_subtract
      · -- sr.sr
        rw [DihedralGroup.sr_mul_sr]
        simp only [HSMul.hSMul, SMul.smul]
        symm
        apply inverseInverse_subtract'


-- @@ L185-185 verbatim
local instance : Scale Pitch Interval := diatonic ⟨.c, .natural⟩ .c


-- @@ L187-192 verbatim
lemma pitch_toZMod12_smul_interval (p : Pitch) (i : Interval) :
  pitch_toZMod12 (i • p) = pitch_toZMod12 p + interval_toZMod12 i := by
  unfold pitch_toZMod12 interval_toZMod12
  simp only [smul_Pitch_Interval_acc, smul_Pitch_Interval_name]
  rw [← nameDistance_image (p.name + i.name) p.name 0]
  grind


-- @@ L194-200 verbatim
lemma pitch_toZMod12_smul_neg_interval (p : Pitch) (i : Interval) :
    pitch_toZMod12 ((-i) • p) =
      pitch_toZMod12 p - interval_toZMod12 i := by
  rw [pitch_toZMod12_smul_interval]
  unfold pitch_toZMod12 interval_toZMod12
  simp only [Interval.instNeg]
  grind


-- @@ L202-208 verbatim
lemma interval_toZMod12_pitch_sub_pitch (p q : Pitch) :
    interval_toZMod12 (p / q) =
      pitch_toZMod12 p - pitch_toZMod12 q := by
  unfold pitch_toZMod12 interval_toZMod12
  simp only [div_Pitch_Pitch_semitones, Accidental.sub_Accidental_semitones]
  rw [← nameDistance_image p.name q.name 0]
  grind


-- @@ L210-233 verbatim
lemma pitch_toZMod12_srInterval (a p : Pitch) (i : Interval) :
    pitch_toZMod12 (srInterval i a p) = 2 * pitch_toZMod12 a - pitch_toZMod12 p - interval_toZMod12 i := by
  unfold srInterval
  have h1 : (-(p / a) - i) = -((p / a) + i) := by
    apply Interval.ext
    unfold HSub.hSub instHSub Sub.sub Interval.instSub
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
    unfold Neg.neg Interval.instNeg
    grind
    unfold HSub.hSub instHSub Sub.sub Interval.instSub
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
    unfold Neg.neg Interval.instNeg
    grind
  rw [h1]
  rw [pitch_toZMod12_smul_neg_interval a ((p / a) + i)]
  have h2 : interval_toZMod12 ((p / a) + i) = interval_toZMod12 (p / a) + interval_toZMod12 i := by
    unfold interval_toZMod12
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
    simp
    rfl
  rw [h2]
  rw [interval_toZMod12_pitch_sub_pitch]
  rw [two_mul]
  grind


-- @@ L235-235 verbatim
def pitchTriad (p : Pitch) (q : Parity) : Triad := (pitch_toZMod12 p, q)


-- @@ L237-239 verbatim
def TransposeAction.mapParity : @TransposeAction Pitch Interval → Parity → Parity
  | .r _, q => q
  | .sr _ _, q => q.flip


-- @@ L241-270 verbatim
theorem transposeAction_toDihedral_triad (t : @TransposeAction Pitch Interval) (p : Pitch) (q : Parity) :
  TransposeAction.toDihedral t • pitchTriad p q = pitchTriad (t • p) (TransposeAction.mapParity t q) := by
  cases t
  apply Prod.ext
  unfold pitchTriad TransposeAction.toDihedral HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad
  simp
  unfold transposeTriad instSMulTransposeAction rInterval
  simp
  rw [pitch_toZMod12_smul_interval]
  unfold pitchTriad TransposeAction.toDihedral TransposeAction.mapParity
  unfold HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad transposeTriad
  simp
  apply Prod.ext
  unfold pitchTriad TransposeAction.toDihedral HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad
  simp
  unfold invertTriad instSMulTransposeAction
  simp
  rw [add_comm]
  rename_i a
  rename_i i
  have : 2 * pitch_toZMod12 i - interval_toZMod12 a + -pitch_toZMod12 p = 2 * pitch_toZMod12 i - pitch_toZMod12 p - interval_toZMod12 a := by
    unfold pitch_toZMod12
    unfold interval_toZMod12
    grind
  rw [this]
  symm
  rw [pitch_toZMod12_srInterval]
  unfold pitchTriad TransposeAction.toDihedral TransposeAction.mapParity
  unfold HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad invertTriad
  simp
