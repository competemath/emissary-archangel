import OAI.InformationTheory.BooleanNoise.Model
import OAI.Combinatorics.GotsmanLinial.Statement
import Mathlib.Analysis.SpecialFunctions.Artanh


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace LeanBlast.CourtadeKumar


-- @@ L11-12 verbatim
def noiseKernel {n : ℕ} (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then (1 + u) / 2 else (1 - u) / 2


-- @@ L14-15 verbatim
def noiseOperator {n : ℕ} (u : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, noiseKernel u x y * g y


-- @@ L17-18 verbatim
abbrev flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  LeanBlast.GotsmanLinial.flip i x


-- @@ L20-21 verbatim
def cubeDerivative {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (g x - g (flip i x)) / 2


-- @@ L23-24 verbatim
def psi (v : ℝ) : ℝ :=
  (1 + v) / 2 * Real.log (1 + v) + (1 - v) / 2 * Real.log (1 - v)


-- @@ L26-26 verbatim
def entropy (v : ℝ) : ℝ := ell - psi v


-- @@ L28-29 verbatim
def entropyAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => entropy (g x))


-- @@ L31-32 verbatim
def informationDeficit {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  entropy (cubeAverage g) - entropyAverage g


-- @@ L34-35 verbatim
def meanVariance {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  1 - (cubeAverage g) ^ 2


-- @@ L37-38 verbatim
def dissipation {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  ∑ i, cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i g x)


-- @@ L40-41 verbatim
def IsInterior {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, -1 < g x ∧ g x < 1


-- @@ L43-44 verbatim
def IsSignValued {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, g x = 1 ∨ g x = -1


-- @@ L46-47 verbatim
def IsIncreasing {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y


-- @@ L49-50 verbatim
def signEncoding {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f x then 1 else -1


-- @@ L52-53 verbatim
def restrict {n : ℕ} (g : Cube (n + 1) → ℝ) (b : Bool) (x : Cube n) : ℝ :=
  g (Fin.cases b x)


-- @@ L55-56 verbatim
def pairMean {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x + restrict g false x) / 2


-- @@ L58-59 verbatim
def pairHalfDifference {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x - restrict g false x) / 2


-- @@ L61-62 verbatim
def pairEntropyGap (a b : ℝ) : ℝ :=
  entropy a - (entropy (a + b) + entropy (a - b)) / 2


-- @@ L64-65 verbatim
def pairDissipation (a b : ℝ) : ℝ :=
  b / 2 * (Real.artanh (a + b) - Real.artanh (a - b))


-- @@ L67-67 verbatim
end LeanBlast.CourtadeKumar


-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
