import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Filter MeasureTheory

-- @@ L7-7 verbatim
open scoped BigOperators Topology ENNReal ContDiff


-- @@ L9-9 verbatim
namespace HarmonicCounterexample


-- @@ L11-11 verbatim
abbrev Space (n : ℕ) := Fin n → ℝ

-- @@ L12-12 verbatim
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ


-- @@ L14-18 verbatim
/-- A genuine smooth positive definite covariant metric tensor on R^n. -/
structure SmoothMetric (n : ℕ) where
  coeff : Space n → Mat n
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x => coeff x i j)
  positive : ∀ x, (coeff x).PosDef


-- @@ L20-22 verbatim
/-- The coordinate directional derivative. -/
def coordDeriv {n : ℕ} (i : Fin n) (f : Space n → ℝ) (x : Space n) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)


-- @@ L24-30 verbatim
/-- Levi-Civita connection in the single global Cartesian chart. -/
def christoffel {n : ℕ} (g : SmoothMetric n) (x : Space n)
    (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (g.coeff x)⁻¹ k l *
    (coordDeriv i (fun y => g.coeff y j l) x +
     coordDeriv j (fun y => g.coeff y i l) x -
     coordDeriv l (fun y => g.coeff y i j) x)


-- @@ L32-37 verbatim
/-- Ricci tensor, with the convention in which the round sphere has positive Ricci. -/
def ricci {n : ℕ} (g : SmoothMetric n) (x : Space n) (i j : Fin n) : ℝ :=
  (∑ k, (coordDeriv k (fun y => christoffel g y k i j) x -
    coordDeriv j (fun y => christoffel g y k i k) x)) +
  ∑ k, ∑ l, (christoffel g x k i j * christoffel g x l k l -
    christoffel g x l i k * christoffel g x k j l)


-- @@ L39-40 verbatim
def RicciNonnegative {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∀ (x v : Space n), 0 ≤ ∑ i, ∑ j, ricci g x i j * v i * v j


-- @@ L42-46 verbatim
/-- Trace of the covariant Hessian, i.e. the Laplace-Beltrami operator. -/
def laplaceBeltrami {n : ℕ} (g : SmoothMetric n) (u : Space n → ℝ)
    (x : Space n) : ℝ :=
  ∑ i, ∑ j, (g.coeff x)⁻¹ i j *
    (coordDeriv i (coordDeriv j u) x - ∑ k, christoffel g x k i j * coordDeriv k u x)


-- @@ L48-51 verbatim
/-- Riemannian length of a path on the unit parameter interval. -/
def pathLength {n : ℕ} (g : SmoothMetric n) (γ : ℝ → Space n) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt
    (∑ i, ∑ j, g.coeff (γ t) i j * deriv γ t i * deriv γ t j)


-- @@ L53-56 verbatim
/-- Infimum of smooth path lengths, the intrinsic Riemannian distance. -/
def distance {n : ℕ} (g : SmoothMetric n) (x y : Space n) : ℝ :=
  sInf {L : ℝ | ∃ γ : ℝ → Space n,
    ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧ L = pathLength g γ}


-- @@ L58-62 verbatim
/-- Sequential metric completeness, for the intrinsic distance, not the background one. -/
def Complete {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∀ z : ℕ → Space n,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, distance g (z p) (z q) < ε) →
    ∃ x : Space n, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, distance g (z p) x < ε


-- @@ L64-65 verbatim
def EuclideanNearOrigin {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x : Space n, (∑ i, x i ^ 2) < ε ^ 2 → g.coeff x = 1


-- @@ L67-70 verbatim
/-- Riemannian measure of the intrinsic open ball, retaining infinite values. -/
def ballVolume {n : ℕ} (g : SmoothMetric n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x : Space n | distance g 0 x < R},
    ENNReal.ofReal (Real.sqrt (g.coeff x).det) ∂volume


-- @@ L72-74 verbatim
/-- The ordinary Euclidean unit ball volume, in Cartesian Lebesgue measure. -/
def omega (n : ℕ) : ℝ≥0∞ :=
  volume {x : Space n | (∑ i, x i ^ 2) < 1}


-- @@ L76-80 verbatim
/-- The volume-ratio limit is finite, positive, and strictly below one. -/
def PositiveSubunitAVR {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    Tendsto (fun R : ℝ => ballVolume g R / (omega n * ENNReal.ofReal (R ^ n)))
      atTop (𝓝 (ENNReal.ofReal a))


-- @@ L82-85 verbatim
/-- Membership in the actual space H_k, with the bound required at every point. -/
def HarmonicGrowth {n : ℕ} (g : SmoothMetric n) (k : ℕ) (u : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ x, laplaceBeltrami g u x = 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C * (1 + distance g 0 x) ^ k



-- @@ L88-89 verbatim
def euclideanDimension (n k : ℕ) : ℕ :=
  (n + k - 1).choose k + (n + k - 2).choose (k - 1)


-- @@ L91-96 verbatim
/-- The manuscript's unconditional main existence claim. -/
def MainClaim : Prop :=
  ∃ (n k : ℕ) (g : SmoothMetric n), Even n ∧ 8 ≤ n ∧ 2 ≤ k ∧
    Complete g ∧ RicciNonnegative g ∧ EuclideanNearOrigin g ∧ PositiveSubunitAVR g ∧
    ∃ u : Fin (euclideanDimension n k + 1) → (Space n → ℝ),
      LinearIndependent ℝ u ∧ ∀ i, HarmonicGrowth g k (u i)




-- @@ L100-100 verbatim
end HarmonicCounterexample


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end OAI
