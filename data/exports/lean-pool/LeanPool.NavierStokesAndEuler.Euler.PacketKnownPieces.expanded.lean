/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderSpatialInvariance
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownJets
import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly


-- @@ L13-13 verbatim
/-! The three actual, strictly known pieces of a recursive velocity jet. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField


-- @@ L22-22 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L24-29 verbatim
/-- The previous corrector carries velocity grade `i` and profile grade `i-1`. -/
inductive KnownPiece where
  | high
  | mean
  | corrector
  deriving DecidableEq


-- @@ L31-33 verbatim
instance : Fintype KnownPiece where
  elems := {.high, .mean, .corrector}
  complete k := by cases k <;> simp


-- @@ L35-35 verbatim
namespace KnownPiece


-- @@ L37-42 verbatim
/-- Active as an element of `Prop`. -/
def active (k : KnownPiece) (p i : ℕ) : Prop :=
  match k with
  | .high => 1 ≤ i ∧ i < p
  | .mean => 2 ≤ i ∧ i < p
  | .corrector => 2 ≤ i ∧ i ≤ p


-- @@ L44-45 verbatim
instance (k : KnownPiece) (p i : ℕ) : Decidable (k.active p i) := by
  cases k <;> unfold active <;> infer_instance


-- @@ L47-51 verbatim
/-- Profile index as an element of `ℕ`. -/
def profileIndex (k : KnownPiece) (i : ℕ) : ℕ :=
  match k with
  | .high | .mean => i
  | .corrector => i-1


-- @@ L53-60 verbatim
/-- Raw, with branches according to `k.active p i`. -/
def raw (k : KnownPiece) (p : ℕ) (a : ℕ → Profile) (i : ℕ) : VectorField :=
  if k.active p i then
    match k with
    | .high => (a i).high
    | .mean => (a i).mean
    | .corrector => (a (i-1)).corrector
  else 0


-- @@ L62-65 verbatim
/-- Jet, given by `slicedJet O.interval (k.raw p a i) z`. -/
def jet (k : KnownPiece) (O : Operators) (p : ℕ) (a : ℕ → Profile)
    (z : Domain) (i : ℕ) : VectorJet :=
  slicedJet O.interval (k.raw p a i) z


-- @@ L67-70 verbatim
theorem jet_zero_of_inactive (k : KnownPiece) (O : Operators) (p : ℕ)
    (a : ℕ → Profile) (z : Domain) (i : ℕ) (hi : ¬ k.active p i) :
    k.jet O p a z i = 0 := by
  simp only [jet, raw, hi, ite_false, slicedJet_zero']


-- @@ L72-74 verbatim
theorem active_profile_lt (k : KnownPiece) (p i : ℕ) (hi : k.active p i) :
    k.profileIndex i < p := by
  cases k <;> simp only [active, profileIndex] at * <;> omega


-- @@ L76-76 verbatim
end KnownPiece


-- @@ L78-100 verbatim
theorem knownJets_eq_pieces (O : Operators) (p : ℕ) (hp : 2 ≤ p)
    (a : ℕ → Profile) (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0)
    (z : Domain) (i : ℕ) :
    knownJets O p a z i = KnownPiece.high.jet O p a z i +
      KnownPiece.mean.jet O p a z i + KnownPiece.corrector.jet O p a z i := by
  by_cases hi0 : i = 0
  · subst i
    simp [knownJets, history, velocityJet, KnownPiece.jet, KnownPiece.raw,
      KnownPiece.active, slicedJet_zero', show 0 < p by omega]
  by_cases hi1 : i = 1
  · subst i
    simp [knownJets, history, velocityJet, KnownPiece.jet, KnownPiece.raw,
      KnownPiece.active, slicedJet_zero', show 1 < p by omega, hc, hb]
  have hi2 : 2 ≤ i := by omega
  by_cases hip : i < p
  · simp [knownJets, history, velocityJet, KnownPiece.jet, KnownPiece.raw,
      KnownPiece.active, hi0, hip, hi2, show 1 ≤ i by omega, show i ≤ p by omega]
  by_cases hie : i = p
  · subst i
    simp [knownJets, history, KnownPiece.jet, KnownPiece.raw, KnownPiece.active,
      slicedJet_zero', hp]
  · simp [knownJets, history, KnownPiece.jet, KnownPiece.raw, KnownPiece.active,
      slicedJet_zero', hip, hie, show ¬ i ≤ p by omega]


-- @@ L102-102 verbatim
variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}


-- @@ L104-116 verbatim
/-- Each masked component remains an actual field from the strict prefix. -/
def PrefixFields.piece (F : PrefixFields P T p a) (k : KnownPiece) (i : ℕ) :
    Field P T (k.raw p a i) := by
  by_cases hi : k.active p i
  · cases k with
    | high =>
      exact (F.high i hi.2).congr (fun _ _ _ => by simp only [KnownPiece.raw, hi, ite_true])
    | mean =>
      exact (F.mean i hi.2).congr (fun _ _ _ => by simp only [KnownPiece.raw, hi, ite_true])
    | corrector =>
      have hp : i-1 < p := by simp only [KnownPiece.active] at hi; omega
      exact (F.corrector (i-1) hp).congr (fun _ _ _ => by simp only [KnownPiece.raw, hi, ite_true])
  · exact (Field.zero P T).congr (fun _ _ _ => by simp only [KnownPiece.raw, hi, ite_false])


-- @@ L118-121 verbatim
/-- Piece jet, given by `SpatialJetField.ofField O.interval (F.piece k i)`. -/
def PrefixFields.pieceJet (F : PrefixFields P T p a) (O : Operators) (k : KnownPiece) (i : ℕ) :
    SpatialJetField P T (fun z => k.jet O p a z i) :=
  SpatialJetField.ofField O.interval (F.piece k i)


-- @@ L123-130 verbatim
theorem KnownPiece.high_tangent
    (h : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      inner ℝ (O.normal (t, (x, θ))) ((a i).high (t, (x, θ))) = 0)
    (i : ℕ) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    inner ℝ (O.normal (t,(x,θ))) ((KnownPiece.high.jet O p a (t,(x,θ)) i).1) = 0 := by
  by_cases hi : KnownPiece.high.active p i
  · simpa only [KnownPiece.jet, KnownPiece.raw, hi, ite_true, slicedJet] using h i hi.2 t x θ
  · simp only [KnownPiece.jet_zero_of_inactive _ _ _ _ _ _ hi, Prod.fst_zero, inner_zero_right]


-- @@ L132-139 verbatim
theorem KnownPiece.mean_angle
    (h : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t, (x, θ)) = (a i).mean (t, (x, 0)))
    (i : ℕ) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    KnownPiece.mean.raw p a i (t,(x,θ)) = KnownPiece.mean.raw p a i (t,(x,0)) := by
  by_cases hi : KnownPiece.mean.active p i
  · simpa only [KnownPiece.raw, hi, ite_true] using h i hi.2 t x θ
  · simp only [KnownPiece.raw, hi, ite_false, Pi.zero_apply]


-- @@ L141-146 verbatim
theorem PrefixFields.meanPiece_angleIndependent (F : PrefixFields P T p a)
    (h : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t, (x, θ)) = (a i).mean (t, (x, 0)))
    (i : ℕ) (t : Icc (0 : ℝ) T) (x : Space) :
    AngleIndependentJet (fun θ => KnownPiece.mean.jet O p a (t,(x,θ)) i) :=
  (F.piece .mean i).slicedJet_angleIndependent O.interval (KnownPiece.mean_angle h i) t x


-- @@ L148-148 verbatim
end EulerPacketCylinderField
