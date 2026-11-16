import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


-- @@ L6-12 verbatim
/-!
# Matrix identities used in the local calculation

All identities hold over an arbitrary field. The symplectic form here is the
anti-diagonal form of the paper, rather than a silently substituted convention.
No Haar measure or representation-theoretic statements are asserted in this file.
-/


-- @@ L14-14 verbatim
namespace FourierJacobi

-- @@ L15-15 verbatim
namespace LocalMatrix


-- @@ L17-17 verbatim
open Matrix

-- @@ L18-18 verbatim
variable {K : Type*} [Field K]


-- @@ L20-21 verbatim
def X (u : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, u, 0, 0; 0, 1, 0, 0; 0, 0, 1, -u; 0, 0, 0, 1]


-- @@ L23-24 verbatim
def YZ (y z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, y, z; 0, 1, 0, y; 0, 0, 1, 0; 0, 0, 0, 1]


-- @@ L26-27 verbatim
def N (x y z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, y, z; 0, 1, x, y; 0, 0, 1, 0; 0, 0, 0, 1]


-- @@ L29-30 verbatim
def D (a : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, a, 0, 0; 0, 0, a⁻¹, 0; 0, 0, 0, 1]


-- @@ L32-33 verbatim
def E (p : K) : Matrix (Fin 4) (Fin 4) K :=
  !![p, 0, 0, 0; 0, 1, 0, 0; 0, 0, p, 0; 0, 0, 0, 1]


-- @@ L35-36 verbatim
def w : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1]


-- @@ L38-39 verbatim
def wInv : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1]


-- @@ L41-42 verbatim
def J : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]


-- @@ L44-44 verbatim
def g (a x y z : K) : Matrix (Fin 4) (Fin 4) K := D a * N x y z


-- @@ L46-49 verbatim
local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g, X, YZ, N, D, E, w, wInv, J, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]))


-- @@ L51-52 verbatim
theorem w_mul_wInv : (w : Matrix (Fin 4) (Fin 4) K) * wInv = 1 := by
  entries


-- @@ L54-55 verbatim
theorem wInv_mul_w : (wInv : Matrix (Fin 4) (Fin 4) K) * w = 1 := by
  entries


-- @@ L57-59 verbatim
theorem g_symplectic (a x y z : K) (ha : a ≠ 0) :
    (g a x y z).transpose * J * g a x y z = J := by
  entries <;> field_simp <;> ring


-- @@ L61-64 verbatim
theorem heisenberg_rearrange (y z u t : K) :
    YZ y z * X u * N (-t) 0 0 =
      N (-t) 0 0 * YZ (y - t * u) (z - t * u ^ 2) * X u := by
  entries <;> ring


-- @@ L66-69 verbatim
theorem remove_two_coordinates (a x y z t r : K) (ha : a ≠ 0) :
    N t 0 0 * X (-r) * g a x y z =
      X (-r) * D a * N (x + t / a ^ 2) (y + r * t / a) (z + r ^ 2 * t) := by
  entries <;> field_simp <;> ring


-- @@ L71-73 verbatim
theorem twist_conjugation (a x y z p : K) (hp : p ≠ 0) :
    E p⁻¹ * g a x y z * E p = D a * N (p * x) y (z / p) := by
  entries <;> field_simp


-- @@ L75-77 verbatim
theorem minus_twist (a x y z : K) :
    E (-1) * g a x y z * E (-1) = D a * N (-x) y (-z) := by
  entries


-- @@ L79-82 verbatim
theorem right_w_twist (a x y z p : K) (ha : a ≠ 0) (hp : p ≠ 0) :
    E p⁻¹ * g a x y z * w * E p =
      D (a * p) * N (x / p) (y / p) (z / p) * w := by
  entries <;> field_simp


-- @@ L84-87 verbatim
theorem left_w_twist (a x y z p : K) (ha : a ≠ 0) (hp : p ≠ 0) :
    E p⁻¹ * wInv * g a x y z * E p =
      wInv * D (a / p) * N (p * x) y (z / p) := by
  entries <;> field_simp


-- @@ L89-92 verbatim
theorem w_conjugation (a x y z : K) :
    wInv * g a x y z * w =
      !![1, -y, 0, z; 0, a⁻¹, 0, 0; 0, -a * x, a, a * y; 0, 0, 0, 1] := by
  entries


-- @@ L94-97 verbatim
theorem w_remove_two_coordinates (a x y z r s : K) (ha : a ≠ 0) :
    YZ r 0 * wInv * N (-s) 0 0 * X (-r) * D a * N x y z * w =
      wInv * D a * N (x - s / a ^ 2) (y - r * s / a) (z - r ^ 2 * s) * w := by
  entries <;> field_simp <;> ring


-- @@ L99-101 verbatim
/-- The six increasing pairs of row or column indices, in lexicographic order. -/
def indexPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


-- @@ L103-107 verbatim
/-- The matrix of all 2 × 2 minors. -/
def secondCompound (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  fun i j =>
    A (indexPairs i).1 (indexPairs j).1 * A (indexPairs i).2 (indexPairs j).2 -
    A (indexPairs i).1 (indexPairs j).2 * A (indexPairs i).2 (indexPairs j).1


-- @@ L109-120 verbatim
theorem all_two_by_two_minors (a x y z : K) (ha : a ≠ 0) :
    secondCompound (g a x y z) =
      !![a, a * x, a * y, -a * y, -a * z, a * (y ^ 2 - x * z);
         0, a⁻¹, 0, 0, 0, -z / a;
         0, 0, 1, 0, 0, y;
         0, 0, 0, 1, 0, -y;
         0, 0, 0, 0, a, a * x;
         0, 0, 0, 0, 0, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondCompound, indexPairs, g, D, N, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> field_simp


-- @@ L122-122 verbatim
end LocalMatrix

-- @@ L123-123 verbatim
end FourierJacobi
