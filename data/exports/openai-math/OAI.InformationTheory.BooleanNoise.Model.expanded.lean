import Mathlib
import OAI.Combinatorics.GotsmanLinial.Model


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators


-- @@ L10-10 verbatim
namespace LeanBlast.CourtadeKumar


-- @@ L12-12 verbatim
abbrev Cube (n : ℕ) := LeanBlast.GotsmanLinial.Cube n


-- @@ L14-15 verbatim
def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n


-- @@ L17-17 verbatim
def ell : ℝ := Real.log 2


-- @@ L19-20 verbatim
def bitFlipKernel {n : ℕ} (ε : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - ε else ε


-- @@ L22-23 verbatim
def jointProbability {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => if f x = b then bitFlipKernel ε x y else 0)


-- @@ L25-26 verbatim
def functionMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) : ℝ :=
  ∑ y, jointProbability ε f b y


-- @@ L28-29 verbatim
def observationMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (y : Cube n) : ℝ :=
  ∑ b : Bool, jointProbability ε f b y


-- @@ L31-31 verbatim
def xlogx (t : ℝ) : ℝ := t * Real.log t


-- @@ L33-34 verbatim
def binaryEntropy (ε : ℝ) : ℝ :=
  -(xlogx ε + xlogx (1 - ε)) / ell


-- @@ L36-42 verbatim
def mutualInformation {n : ℕ} (ε : ℝ) (f : Cube n → Bool) : ℝ :=
  (∑ b : Bool, ∑ y : Cube n,
    if 0 < jointProbability ε f b y then
      jointProbability ε f b y *
        Real.log (jointProbability ε f b y /
          (functionMarginal ε f b * observationMarginal ε f y))
    else 0) / ell


-- @@ L44-44 verbatim
def dictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := x i


-- @@ L46-46 verbatim
def complementDictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := !(x i)


-- @@ L48-51 verbatim
def CourtadeKumarStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ f : Cube n → Bool, mutualInformation ε f ≤ 1 - binaryEntropy ε


-- @@ L53-58 verbatim
def DictatorAttainmentStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ i : Fin n,
        mutualInformation ε (dictator i) = 1 - binaryEntropy ε ∧
        mutualInformation ε (complementDictator i) = 1 - binaryEntropy ε


-- @@ L60-60 verbatim
def FullStatement : Prop := CourtadeKumarStatement ∧ DictatorAttainmentStatement


-- @@ L62-62 verbatim
end LeanBlast.CourtadeKumar


-- @@ L64-64 verbatim
end


-- @@ L66-66 verbatim
end OAI
