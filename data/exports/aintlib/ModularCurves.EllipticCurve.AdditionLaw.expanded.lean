/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.Jacobson.Ring


-- @@ L9-40 verbatim
/-!
# The second Bosma–Lenstra addition law in projective coordinates (T-W7.0c-i)

Mathlib's `WeierstrassCurve.Projective.addX/addY/addZ` is the Bosma–Lenstra addition law of
the line `Z = 0` (law 1) — exceptional exactly on the diagonal. This file supplies the
**second** law of the complete pair (B–L Thm 2: the law of the line `Y = 0`), `dblAddX/Y/Z`
("the addition law that extends doubling"), and the certified identities linking the two:

* the three cross-law 2×2 minors vanish modulo the two curve equations (the laws are
  projectively proportional on the overlap of their domains) — `…_minor_XY/XZ/YZ`;
* the diagonal of law 2 **is** mathlib's doubling `dblX/dblY/dblZ` — `dblAdd*_self`;
* the `O`-columns: law 2 computes `O + Q = Q` and `P + O = P` with no curve hypothesis;
* bihomogeneity of bidegree `(2, 2)` — `dblAdd*_smul`.

## Provenance (source-of-record: `projects/ModularCurves/scripts/tw7-p1-bosma-lenstra/`)

Law 2 was **derived, not transcribed** — solved exactly from the paper's anchor
`law2ᵢ = s*(Y/Z)·law1ᵢ` (Bosma–Lenstra, *Complete systems of two addition laws for elliptic
curves*, J. Number Theory 53 (1995), p. 237; verbatim quotes with locators in
`.mathlib-quality/tw7-source-quotes.md`) by mod-p interpolation over the graded (2,2)-monomial
basis with integer lift, then certified by the exact ideal identity and 25 end-to-end numeric
group-law checks (`derive_law2.py`). The derivation surfaced a discrepancy against a reading
of the printed `X₃⁽²⁾` on p. 237 — see the warning on `dblAddX`; the derived polynomials are
authoritative independently of anyone's reading of the printed page (the derivation is
overdetermined). Every `linear_combination` cofactor below is kernel-checked here — the CAS
is a search procedure, not a trust step.

The remaining B–L facts are NOT certificates by design (certificate policy, board
T-W7.0c-i): law 2 landing on the curve (c5) and law 1's `equation_addXYZ` route through the
generic-point engine — tickets T-W7.0c-c5α (factorization bridge; skeleton `eq_zero_of_`
`forall_isMaximal_mem` below) and T-W7.0c-c5β (triple → morphism plumbing).
-/


-- @@ L42-42 verbatim
local notation3 "x" => (0 : Fin 3)


-- @@ L44-44 verbatim
local notation3 "y" => (1 : Fin 3)


-- @@ L46-46 verbatim
local notation3 "z" => (2 : Fin 3)


-- @@ L48-50 verbatim
local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])


-- @@ L52-52 verbatim
namespace WeierstrassCurve.Projective


-- @@ L54-54 verbatim
variable {R : Type*} [CommRing R] {W' : Projective R}


-- @@ L56-56 verbatim
/-! ## The law of the line `Y = 0` -/


-- @@ L58-98 expanded
variable (W') in
/-- The `X`-coordinate of the second Bosma–Lenstra addition law (the law of the line `Y = 0`),
evaluated at two projective point representatives `P` and `Q`. Its diagonal is `dblX`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring).

**Paper-fidelity warning — do NOT "correct" this polynomial against the printed page.** In
the printed `X₃⁽²⁾` (B–L p. 237; paper coordinates `P = (X₁:Y₁:Z₁)`, `Q = (X₂:Y₂:Z₂)`), the
`a₃a₄` term is easily (mis)read as `+ a₃a₄·(X₁Z₂ − 2X₂Z₁)·X₂Z₁`. The true term, as derived
and certified here, is `− a₃a₄·(2X₁Z₂ + X₂Z₁)·X₂Z₁` — the two monomials
`- 2 * W'.a₃ * W'.a₄ * P x * P z * Q x * Q z - W'.a₃ * W'.a₄ * P z ^ 2 * Q x ^ 2` below.
The derivation is overdetermined (exact anchor ideal identity `d³Z₁Z₂·law2ᵢ ≡ N_Y·law1ᵢ`
plus 25 independent end-to-end numeric group-law samples; `derive_law2.py`), so the stored
polynomial is authoritative independently of any reading of the page — and the six
kernel-checked certificates in this file would all fail against the misread variant. -/
noncomputable def dblAddX (P Q : Fin 3 → R) : R :=
  -W'.a₁ * W'.a₂ * P (0 : Fin 3) ^ 2 * Q (0 : Fin 3) ^ 2 -
                                                                                                                W'.a₂ *
                                                                                                                      P
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 *
                                                                                                                    Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                    (1 :
                                                                                                                      Fin
                                                                                                                        3) -
                                                                                                              W'.a₁ ^
                                                                                                                        2 *
                                                                                                                      W'.a₃ *
                                                                                                                    P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 *
                                                                                                                  Q
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) -
                                                                                                            2 *
                                                                                                                      W'.a₁ *
                                                                                                                    W'.a₄ *
                                                                                                                  P
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    2 *
                                                                                                                Q
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) -
                                                                                                          W'.a₁ *
                                                                                                                  W'.a₃ *
                                                                                                                P
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) ^
                                                                                                                  2 *
                                                                                                              Q
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) -
                                                                                                        W'.a₄ *
                                                                                                              P
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                2 *
                                                                                                            Q
                                                                                                              (1 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) -
                                                                                                      W'.a₁ *
                                                                                                            W'.a₃ ^
                                                                                                              2 *
                                                                                                          P
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 *
                                                                                                        Q
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          2 -
                                                                                                    3 *
                                                                                                            W'.a₁ *
                                                                                                          W'.a₆ *
                                                                                                        P
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          2 *
                                                                                                      Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        2 +
                                                                                                  W'.a₁ ^
                                                                                                          2 *
                                                                                                        P
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      P
                                                                                                        (1 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      2 -
                                                                                                W'.a₂ *
                                                                                                      P
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    P
                                                                                                      (1 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    2 +
                                                                                              2 *
                                                                                                        W'.a₁ *
                                                                                                      P
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    P
                                                                                                      (1 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                  (1 :
                                                                                                    Fin
                                                                                                      3) -
                                                                                            2 *
                                                                                                      W'.a₄ *
                                                                                                    P
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  P
                                                                                                    (1 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) +
                                                                                          P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                              P
                                                                                                (1 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                                (1 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              2 -
                                                                                        W'.a₃ ^ 2 *
                                                                                              P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            P
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            2 -
                                                                                      3 * W'.a₆ *
                                                                                            P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          P
                                                                                            (1 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          2 -
                                                                                    W'.a₁ * W'.a₄ *
                                                                                          P
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) *
                                                                                        P
                                                                                          (2 :
                                                                                            Fin 3) *
                                                                                      Q
                                                                                          (0 :
                                                                                            Fin 3) ^
                                                                                        2 -
                                                                                  W'.a₂ * W'.a₃ *
                                                                                        P
                                                                                          (0 :
                                                                                            Fin 3) *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) ^
                                                                                      2 -
                                                                                2 * W'.a₄ *
                                                                                        P
                                                                                          (0 :
                                                                                            Fin 3) *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) *
                                                                                  Q (1 : Fin 3) -
                                                                              2 * W'.a₁ *
                                                                                        W'.a₃ ^ 2 *
                                                                                      P
                                                                                        (0 :
                                                                                          Fin 3) *
                                                                                    P (2 : Fin 3) *
                                                                                  Q (0 : Fin 3) *
                                                                                Q (2 : Fin 3) -
                                                                            6 * W'.a₁ * W'.a₆ *
                                                                                    P (0 : Fin 3) *
                                                                                  P (2 : Fin 3) *
                                                                                Q (0 : Fin 3) *
                                                                              Q (2 : Fin 3) -
                                                                          2 * W'.a₃ * W'.a₄ *
                                                                                  P (0 : Fin 3) *
                                                                                P (2 : Fin 3) *
                                                                              Q (0 : Fin 3) *
                                                                            Q (2 : Fin 3) -
                                                                        2 * W'.a₃ ^ 2 *
                                                                                P (0 : Fin 3) *
                                                                              P (2 : Fin 3) *
                                                                            Q (1 : Fin 3) *
                                                                          Q (2 : Fin 3) -
                                                                      6 * W'.a₆ * P (0 : Fin 3) *
                                                                            P (2 : Fin 3) *
                                                                          Q (1 : Fin 3) *
                                                                        Q (2 : Fin 3) -
                                                                    W'.a₁ ^ 3 * W'.a₆ *
                                                                          P (0 : Fin 3) *
                                                                        P (2 : Fin 3) *
                                                                      Q (2 : Fin 3) ^ 2 +
                                                                  W'.a₁ ^ 2 * W'.a₃ * W'.a₄ *
                                                                        P (0 : Fin 3) *
                                                                      P (2 : Fin 3) *
                                                                    Q (2 : Fin 3) ^ 2 -
                                                                W'.a₁ * W'.a₂ * W'.a₃ ^ 2 *
                                                                      P (0 : Fin 3) *
                                                                    P (2 : Fin 3) *
                                                                  Q (2 : Fin 3) ^ 2 -
                                                              4 * W'.a₁ * W'.a₂ * W'.a₆ *
                                                                    P (0 : Fin 3) *
                                                                  P (2 : Fin 3) *
                                                                Q (2 : Fin 3) ^ 2 +
                                                            W'.a₁ * W'.a₄ ^ 2 * P (0 : Fin 3) *
                                                                P (2 : Fin 3) *
                                                              Q (2 : Fin 3) ^ 2 -
                                                          W'.a₃ ^ 3 * P (0 : Fin 3) *
                                                              P (2 : Fin 3) *
                                                            Q (2 : Fin 3) ^ 2 -
                                                        3 * W'.a₃ * W'.a₆ * P (0 : Fin 3) *
                                                            P (2 : Fin 3) *
                                                          Q (2 : Fin 3) ^ 2 +
                                                      W'.a₁ * P (1 : Fin 3) ^ 2 *
                                                        Q (0 : Fin 3) ^ 2 +
                                                    P (1 : Fin 3) ^ 2 * Q (0 : Fin 3) *
                                                      Q (1 : Fin 3) +
                                                  W'.a₃ * P (1 : Fin 3) ^ 2 * Q (0 : Fin 3) *
                                                    Q (2 : Fin 3) +
                                                W'.a₁ * W'.a₃ * P (1 : Fin 3) * P (2 : Fin 3) *
                                                  Q (0 : Fin 3) ^ 2 -
                                              W'.a₄ * P (1 : Fin 3) * P (2 : Fin 3) *
                                                Q (0 : Fin 3) ^ 2 +
                                            2 * W'.a₃ * P (1 : Fin 3) * P (2 : Fin 3) *
                                                Q (0 : Fin 3) *
                                              Q (1 : Fin 3) -
                                          6 * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) *
                                              Q (0 : Fin 3) *
                                            Q (2 : Fin 3) -
                                        W'.a₁ ^ 2 * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) *
                                          Q (2 : Fin 3) ^ 2 +
                                      W'.a₁ * W'.a₃ * W'.a₄ * P (1 : Fin 3) * P (2 : Fin 3) *
                                        Q (2 : Fin 3) ^ 2 -
                                    W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) *
                                      Q (2 : Fin 3) ^ 2 -
                                  4 * W'.a₂ * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) *
                                    Q (2 : Fin 3) ^ 2 +
                                W'.a₄ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) * Q (2 : Fin 3) ^ 2 -
                              W'.a₃ * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) ^ 2 -
                            3 * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (1 : Fin 3) -
                          W'.a₃ ^ 3 * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (2 : Fin 3) -
                        6 * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (2 : Fin 3) -
                      W'.a₁ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) +
                    W'.a₁ * W'.a₃ * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) -
                  W'.a₂ * W'.a₃ ^ 2 * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) -
                4 * W'.a₂ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) +
              W'.a₄ ^ 2 * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) -
            W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
          W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
        W'.a₂ * W'.a₃ ^ 3 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
      4 * W'.a₂ * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
    W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2


-- @@ L100-140 expanded
variable (W') in
/-- The `Y`-coordinate of the second Bosma–Lenstra addition law; diagonal `dblY`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring). -/
noncomputable def dblAddY (P Q : Fin 3 → R) : R :=
  -W'.a₂ ^ 2 * P (0 : Fin 3) ^ 2 * Q (0 : Fin 3) ^ 2 +
                                                                                                                                                    3 *
                                                                                                                                                          W'.a₄ *
                                                                                                                                                        P
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) ^
                                                                                                                                                          2 *
                                                                                                                                                      Q
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) ^
                                                                                                                                                        2 +
                                                                                                                                                  W'.a₁ ^
                                                                                                                                                            2 *
                                                                                                                                                          W'.a₄ *
                                                                                                                                                        P
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) ^
                                                                                                                                                          2 *
                                                                                                                                                      Q
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) *
                                                                                                                                                    Q
                                                                                                                                                      (2 :
                                                                                                                                                        Fin
                                                                                                                                                          3) -
                                                                                                                                                2 *
                                                                                                                                                            W'.a₁ *
                                                                                                                                                          W'.a₂ *
                                                                                                                                                        W'.a₃ *
                                                                                                                                                      P
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) ^
                                                                                                                                                        2 *
                                                                                                                                                    Q
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) *
                                                                                                                                                  Q
                                                                                                                                                    (2 :
                                                                                                                                                      Fin
                                                                                                                                                        3) -
                                                                                                                                              W'.a₂ *
                                                                                                                                                      W'.a₄ *
                                                                                                                                                    P
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) ^
                                                                                                                                                      2 *
                                                                                                                                                  Q
                                                                                                                                                    (0 :
                                                                                                                                                      Fin
                                                                                                                                                        3) *
                                                                                                                                                Q
                                                                                                                                                  (2 :
                                                                                                                                                    Fin
                                                                                                                                                      3) +
                                                                                                                                            3 *
                                                                                                                                                    W'.a₃ ^
                                                                                                                                                      2 *
                                                                                                                                                  P
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    2 *
                                                                                                                                                Q
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) *
                                                                                                                                              Q
                                                                                                                                                (2 :
                                                                                                                                                  Fin
                                                                                                                                                    3) +
                                                                                                                                          9 *
                                                                                                                                                  W'.a₆ *
                                                                                                                                                P
                                                                                                                                                    (0 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  2 *
                                                                                                                                              Q
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) *
                                                                                                                                            Q
                                                                                                                                              (2 :
                                                                                                                                                Fin
                                                                                                                                                  3) +
                                                                                                                                        3 *
                                                                                                                                                W'.a₁ ^
                                                                                                                                                  2 *
                                                                                                                                              W'.a₆ *
                                                                                                                                            P
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              2 *
                                                                                                                                          Q
                                                                                                                                              (2 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            2 -
                                                                                                                                      2 *
                                                                                                                                                W'.a₁ *
                                                                                                                                              W'.a₃ *
                                                                                                                                            W'.a₄ *
                                                                                                                                          P
                                                                                                                                              (0 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            2 *
                                                                                                                                        Q
                                                                                                                                            (2 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          2 +
                                                                                                                                    W'.a₂ *
                                                                                                                                          W'.a₃ ^
                                                                                                                                            2 *
                                                                                                                                        P
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          2 *
                                                                                                                                      Q
                                                                                                                                          (2 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        2 +
                                                                                                                                  3 *
                                                                                                                                          W'.a₂ *
                                                                                                                                        W'.a₆ *
                                                                                                                                      P
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        2 *
                                                                                                                                    Q
                                                                                                                                        (2 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      2 -
                                                                                                                                W'.a₄ ^
                                                                                                                                      2 *
                                                                                                                                    P
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      2 *
                                                                                                                                  Q
                                                                                                                                      (2 :
                                                                                                                                        Fin
                                                                                                                                          3) ^
                                                                                                                                    2 +
                                                                                                                              W'.a₁ *
                                                                                                                                      W'.a₂ *
                                                                                                                                    P
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  P
                                                                                                                                    (1 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                Q
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) ^
                                                                                                                                  2 -
                                                                                                                            3 *
                                                                                                                                    W'.a₃ *
                                                                                                                                  P
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                P
                                                                                                                                  (1 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 +
                                                                                                                          2 *
                                                                                                                                      W'.a₁ *
                                                                                                                                    W'.a₄ *
                                                                                                                                  P
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                P
                                                                                                                                  (1 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) *
                                                                                                                            Q
                                                                                                                              (2 :
                                                                                                                                Fin
                                                                                                                                  3) -
                                                                                                                        2 *
                                                                                                                                    W'.a₂ *
                                                                                                                                  W'.a₃ *
                                                                                                                                P
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              P
                                                                                                                                (1 :
                                                                                                                                  Fin
                                                                                                                                    3) *
                                                                                                                            Q
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) *
                                                                                                                          Q
                                                                                                                            (2 :
                                                                                                                              Fin
                                                                                                                                3) +
                                                                                                                      3 *
                                                                                                                                W'.a₁ *
                                                                                                                              W'.a₆ *
                                                                                                                            P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) *
                                                                                                                          P
                                                                                                                            (1 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        Q
                                                                                                                            (2 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 -
                                                                                                                    W'.a₃ *
                                                                                                                            W'.a₄ *
                                                                                                                          P
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        P
                                                                                                                          (1 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      Q
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 -
                                                                                                                  W'.a₂ *
                                                                                                                          W'.a₄ *
                                                                                                                        P
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      P
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 +
                                                                                                                9 *
                                                                                                                        W'.a₆ *
                                                                                                                      P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    P
                                                                                                                      (2 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    2 +
                                                                                                              6 *
                                                                                                                          W'.a₁ ^
                                                                                                                            2 *
                                                                                                                        W'.a₆ *
                                                                                                                      P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    P
                                                                                                                      (2 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) -
                                                                                                            4 *
                                                                                                                          W'.a₁ *
                                                                                                                        W'.a₃ *
                                                                                                                      W'.a₄ *
                                                                                                                    P
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  P
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) +
                                                                                                          2 *
                                                                                                                      W'.a₂ *
                                                                                                                    W'.a₃ ^
                                                                                                                      2 *
                                                                                                                  P
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                P
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) +
                                                                                                        12 *
                                                                                                                    W'.a₂ *
                                                                                                                  W'.a₆ *
                                                                                                                P
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              P
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) -
                                                                                                      4 *
                                                                                                                W'.a₄ ^
                                                                                                                  2 *
                                                                                                              P
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            P
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) +
                                                                                                    W'.a₁ ^
                                                                                                              4 *
                                                                                                            W'.a₆ *
                                                                                                          P
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        P
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        2 -
                                                                                                  W'.a₁ ^
                                                                                                              3 *
                                                                                                            W'.a₃ *
                                                                                                          W'.a₄ *
                                                                                                        P
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      P
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      2 +
                                                                                                W'.a₁ ^
                                                                                                            2 *
                                                                                                          W'.a₂ *
                                                                                                        W'.a₃ ^
                                                                                                          2 *
                                                                                                      P
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    P
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    2 +
                                                                                              5 *
                                                                                                          W'.a₁ ^
                                                                                                            2 *
                                                                                                        W'.a₂ *
                                                                                                      W'.a₆ *
                                                                                                    P
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  P
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  2 -
                                                                                            W'.a₁ ^
                                                                                                      2 *
                                                                                                    W'.a₄ ^
                                                                                                      2 *
                                                                                                  P
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                P
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              Q
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                2 -
                                                                                          W'.a₁ *
                                                                                                      W'.a₂ *
                                                                                                    W'.a₃ *
                                                                                                  W'.a₄ *
                                                                                                P
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              P
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              2 -
                                                                                        W'.a₁ *
                                                                                                W'.a₃ ^
                                                                                                  3 *
                                                                                              P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            P
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            2 -
                                                                                      3 * W'.a₁ *
                                                                                                W'.a₃ *
                                                                                              W'.a₆ *
                                                                                            P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          P
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          2 +
                                                                                    W'.a₂ ^ 2 *
                                                                                            W'.a₃ ^
                                                                                              2 *
                                                                                          P
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) *
                                                                                        P
                                                                                          (2 :
                                                                                            Fin 3) *
                                                                                      Q
                                                                                          (2 :
                                                                                            Fin 3) ^
                                                                                        2 +
                                                                                  4 * W'.a₂ ^ 2 *
                                                                                          W'.a₆ *
                                                                                        P
                                                                                          (0 :
                                                                                            Fin 3) *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (2 : Fin 3) ^
                                                                                      2 -
                                                                                W'.a₂ * W'.a₄ ^ 2 *
                                                                                      P
                                                                                        (0 :
                                                                                          Fin 3) *
                                                                                    P (2 : Fin 3) *
                                                                                  Q (2 : Fin 3) ^
                                                                                    2 -
                                                                              W'.a₃ ^ 2 * W'.a₄ *
                                                                                    P (0 : Fin 3) *
                                                                                  P (2 : Fin 3) *
                                                                                Q (2 : Fin 3) ^ 2 -
                                                                            3 * W'.a₄ * W'.a₆ *
                                                                                  P (0 : Fin 3) *
                                                                                P (2 : Fin 3) *
                                                                              Q (2 : Fin 3) ^ 2 +
                                                                          W'.a₁ *
                                                                                P (1 : Fin 3) ^ 2 *
                                                                              Q (0 : Fin 3) *
                                                                            Q (1 : Fin 3) +
                                                                        P (1 : Fin 3) ^ 2 *
                                                                          Q (1 : Fin 3) ^ 2 +
                                                                      W'.a₃ * P (1 : Fin 3) ^ 2 *
                                                                          Q (1 : Fin 3) *
                                                                        Q (2 : Fin 3) +
                                                                    W'.a₁ * W'.a₄ * P (1 : Fin 3) *
                                                                        P (2 : Fin 3) *
                                                                      Q (0 : Fin 3) ^ 2 -
                                                                  W'.a₂ * W'.a₃ * P (1 : Fin 3) *
                                                                      P (2 : Fin 3) *
                                                                    Q (0 : Fin 3) ^ 2 +
                                                                6 * W'.a₁ * W'.a₆ * P (1 : Fin 3) *
                                                                      P (2 : Fin 3) *
                                                                    Q (0 : Fin 3) *
                                                                  Q (2 : Fin 3) -
                                                              2 * W'.a₃ * W'.a₄ * P (1 : Fin 3) *
                                                                    P (2 : Fin 3) *
                                                                  Q (0 : Fin 3) *
                                                                Q (2 : Fin 3) +
                                                            W'.a₁ ^ 3 * W'.a₆ * P (1 : Fin 3) *
                                                                P (2 : Fin 3) *
                                                              Q (2 : Fin 3) ^ 2 -
                                                          W'.a₁ ^ 2 * W'.a₃ * W'.a₄ *
                                                                P (1 : Fin 3) *
                                                              P (2 : Fin 3) *
                                                            Q (2 : Fin 3) ^ 2 +
                                                        W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) *
                                                            P (2 : Fin 3) *
                                                          Q (2 : Fin 3) ^ 2 +
                                                      4 * W'.a₁ * W'.a₂ * W'.a₆ * P (1 : Fin 3) *
                                                          P (2 : Fin 3) *
                                                        Q (2 : Fin 3) ^ 2 -
                                                    W'.a₁ * W'.a₄ ^ 2 * P (1 : Fin 3) *
                                                        P (2 : Fin 3) *
                                                      Q (2 : Fin 3) ^ 2 -
                                                  W'.a₃ ^ 3 * P (1 : Fin 3) * P (2 : Fin 3) *
                                                    Q (2 : Fin 3) ^ 2 -
                                                3 * W'.a₃ * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) *
                                                  Q (2 : Fin 3) ^ 2 +
                                              3 * W'.a₂ * W'.a₆ * P (2 : Fin 3) ^ 2 *
                                                Q (0 : Fin 3) ^ 2 -
                                            W'.a₄ ^ 2 * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) ^ 2 +
                                          W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P (2 : Fin 3) ^ 2 *
                                              Q (0 : Fin 3) *
                                            Q (2 : Fin 3) -
                                        W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P (2 : Fin 3) ^ 2 *
                                            Q (0 : Fin 3) *
                                          Q (2 : Fin 3) +
                                      3 * W'.a₁ * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 *
                                          Q (0 : Fin 3) *
                                        Q (2 : Fin 3) +
                                    W'.a₂ ^ 2 * W'.a₃ ^ 2 * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) *
                                      Q (2 : Fin 3) +
                                  4 * W'.a₂ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) *
                                    Q (2 : Fin 3) -
                                W'.a₂ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) *
                                  Q (2 : Fin 3) -
                              2 * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) *
                                Q (2 : Fin 3) -
                            3 * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (2 : Fin 3) +
                          W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
                        W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
                      W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
                    W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
                  4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
                2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
              W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
            4 * W'.a₂ * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
          W'.a₃ ^ 4 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
        6 * W'.a₃ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
      W'.a₄ ^ 3 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 -
    9 * W'.a₆ ^ 2 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2


-- @@ L142-163 expanded
variable (W') in
/-- The `Z`-coordinate of the second Bosma–Lenstra addition law; diagonal `dblZ`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring). -/
noncomputable def dblAddZ (P Q : Fin 3 → R) : R :=
  3 * W'.a₁ * P (0 : Fin 3) ^ 2 * Q (0 : Fin 3) ^ 2 +
                                                                                      3 *
                                                                                            P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              2 *
                                                                                          Q
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                          (1 :
                                                                                            Fin 3) +
                                                                                    W'.a₁ ^ 3 *
                                                                                          P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            2 *
                                                                                        Q
                                                                                          (0 :
                                                                                            Fin 3) *
                                                                                      Q
                                                                                        (2 :
                                                                                          Fin 3) +
                                                                                  2 * W'.a₁ *
                                                                                          W'.a₂ *
                                                                                        P
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          2 *
                                                                                      Q
                                                                                        (0 :
                                                                                          Fin 3) *
                                                                                    Q (2 : Fin 3) +
                                                                                W'.a₁ ^ 2 *
                                                                                      P
                                                                                          (0 :
                                                                                            Fin 3) ^
                                                                                        2 *
                                                                                    Q (1 : Fin 3) *
                                                                                  Q (2 : Fin 3) +
                                                                              W'.a₂ *
                                                                                    P (0 : Fin 3) ^
                                                                                      2 *
                                                                                  Q (1 : Fin 3) *
                                                                                Q (2 : Fin 3) +
                                                                            W'.a₁ ^ 2 * W'.a₃ *
                                                                                P (0 : Fin 3) ^ 2 *
                                                                              Q (2 : Fin 3) ^ 2 +
                                                                          W'.a₁ * W'.a₄ *
                                                                              P (0 : Fin 3) ^ 2 *
                                                                            Q (2 : Fin 3) ^ 2 +
                                                                        3 * P (0 : Fin 3) *
                                                                            P (1 : Fin 3) *
                                                                          Q (0 : Fin 3) ^ 2 +
                                                                      2 * W'.a₁ ^ 2 *
                                                                              P (0 : Fin 3) *
                                                                            P (1 : Fin 3) *
                                                                          Q (0 : Fin 3) *
                                                                        Q (2 : Fin 3) +
                                                                    2 * W'.a₂ * P (0 : Fin 3) *
                                                                          P (1 : Fin 3) *
                                                                        Q (0 : Fin 3) *
                                                                      Q (2 : Fin 3) +
                                                                  2 * W'.a₁ * P (0 : Fin 3) *
                                                                        P (1 : Fin 3) *
                                                                      Q (1 : Fin 3) *
                                                                    Q (2 : Fin 3) +
                                                                2 * W'.a₁ * W'.a₃ * P (0 : Fin 3) *
                                                                    P (1 : Fin 3) *
                                                                  Q (2 : Fin 3) ^ 2 +
                                                              W'.a₄ * P (0 : Fin 3) *
                                                                  P (1 : Fin 3) *
                                                                Q (2 : Fin 3) ^ 2 +
                                                            W'.a₁ * W'.a₂ * P (0 : Fin 3) *
                                                                P (2 : Fin 3) *
                                                              Q (0 : Fin 3) ^ 2 +
                                                          3 * W'.a₃ * P (0 : Fin 3) *
                                                              P (2 : Fin 3) *
                                                            Q (0 : Fin 3) ^ 2 +
                                                        2 * W'.a₂ * P (0 : Fin 3) * P (2 : Fin 3) *
                                                            Q (0 : Fin 3) *
                                                          Q (1 : Fin 3) +
                                                      2 * W'.a₁ ^ 2 * W'.a₃ * P (0 : Fin 3) *
                                                            P (2 : Fin 3) *
                                                          Q (0 : Fin 3) *
                                                        Q (2 : Fin 3) +
                                                    2 * W'.a₁ * W'.a₄ * P (0 : Fin 3) *
                                                          P (2 : Fin 3) *
                                                        Q (0 : Fin 3) *
                                                      Q (2 : Fin 3) +
                                                  2 * W'.a₂ * W'.a₃ * P (0 : Fin 3) *
                                                        P (2 : Fin 3) *
                                                      Q (0 : Fin 3) *
                                                    Q (2 : Fin 3) +
                                                2 * W'.a₁ * W'.a₃ * P (0 : Fin 3) * P (2 : Fin 3) *
                                                    Q (1 : Fin 3) *
                                                  Q (2 : Fin 3) +
                                              2 * W'.a₄ * P (0 : Fin 3) * P (2 : Fin 3) *
                                                  Q (1 : Fin 3) *
                                                Q (2 : Fin 3) +
                                            2 * W'.a₁ * W'.a₃ ^ 2 * P (0 : Fin 3) * P (2 : Fin 3) *
                                              Q (2 : Fin 3) ^ 2 +
                                          3 * W'.a₁ * W'.a₆ * P (0 : Fin 3) * P (2 : Fin 3) *
                                            Q (2 : Fin 3) ^ 2 +
                                        W'.a₃ * W'.a₄ * P (0 : Fin 3) * P (2 : Fin 3) *
                                          Q (2 : Fin 3) ^ 2 +
                                      W'.a₁ * P (1 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (2 : Fin 3) +
                                    P (1 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) +
                                  W'.a₃ * P (1 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
                                W'.a₂ * P (1 : Fin 3) * P (2 : Fin 3) * Q (0 : Fin 3) ^ 2 +
                              2 * W'.a₁ * W'.a₃ * P (1 : Fin 3) * P (2 : Fin 3) * Q (0 : Fin 3) *
                                Q (2 : Fin 3) +
                            2 * W'.a₄ * P (1 : Fin 3) * P (2 : Fin 3) * Q (0 : Fin 3) *
                              Q (2 : Fin 3) +
                          P (1 : Fin 3) * P (2 : Fin 3) * Q (1 : Fin 3) ^ 2 +
                        2 * W'.a₃ * P (1 : Fin 3) * P (2 : Fin 3) * Q (1 : Fin 3) * Q (2 : Fin 3) +
                      2 * W'.a₃ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) * Q (2 : Fin 3) ^ 2 +
                    3 * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) * Q (2 : Fin 3) ^ 2 +
                  W'.a₂ * W'.a₃ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) ^ 2 +
                W'.a₄ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (1 : Fin 3) +
              W'.a₁ * W'.a₃ ^ 2 * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (2 : Fin 3) +
            2 * W'.a₃ * W'.a₄ * P (2 : Fin 3) ^ 2 * Q (0 : Fin 3) * Q (2 : Fin 3) +
          W'.a₃ ^ 2 * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) +
        3 * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (1 : Fin 3) * Q (2 : Fin 3) +
      W'.a₃ ^ 3 * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2 +
    3 * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 2 * Q (2 : Fin 3) ^ 2


-- @@ L165-168 verbatim
variable (W') in
/-- The second Bosma–Lenstra addition law as a point representative. -/
noncomputable def dblAddXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblAddX P Q, W'.dblAddY P Q, W'.dblAddZ P Q]


-- @@ L170-175 verbatim
/-- Unfold both addition laws and mathlib's doubling to raw polynomials (for the
`linear_combination` normalization steps below). -/
local macro "law_simp" : tactic =>
  `(tactic| simp only [addX, addY, negAddY, addZ, dblAddX, dblAddY, dblAddZ, dblX, dblY,
    negDblY, dblZ, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons])


-- @@ L177-177 verbatim
/-! ## Bihomogeneity (bidegree `(2, 2)`) -/


-- @@ L179-182 verbatim
lemma dblAddX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddX (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddX P Q := by
  simp only [dblAddX, smul_fin3_ext]
  ring1


-- @@ L184-187 verbatim
lemma dblAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddY P Q := by
  simp only [dblAddY, smul_fin3_ext]
  ring1


-- @@ L189-192 verbatim
lemma dblAddZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddZ (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddZ P Q := by
  simp only [dblAddZ, smul_fin3_ext]
  ring1


-- @@ L194-202 verbatim
/-- **(bidegree `(2,2)`, triple form)** The second Bosma-Lenstra law is bihomogeneous of bidegree
`(2,2)`, exactly as mathlib's first law (`addXYZ_smul`). This is what makes the law descend to
`P² × P² ⇢ P²`: rescaling either projective representative rescales the output triple, so the
resulting point of `P²` is unchanged. It is the reason the per-chart-product morphisms agree on
overlaps of chart-products, where the two representatives differ by the transition scalars. -/
lemma dblAddXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.dblAddXYZ P Q := by
  rw [dblAddXYZ, dblAddX_smul, dblAddY_smul, dblAddZ_smul, smul_fin3, dblAddXYZ]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]


-- @@ L204-204 verbatim
/-! ## The `O`-columns: `O + Q = Q` and `P + O = P`, projectively, with no curve hypothesis -/


-- @@ L206-208 expanded
lemma dblAddX_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddX ![0, Y₁, 0] Q =
      Y₁ ^ 2 * ((W'.a₁ * Q (0 : Fin 3) + Q (1 : Fin 3) + W'.a₃ * Q (2 : Fin 3)) * Q (0 : Fin 3)) :=
  by rw [dblAddX];
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
  ring1


-- @@ L210-212 expanded
lemma dblAddY_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddY ![0, Y₁, 0] Q =
      Y₁ ^ 2 * ((W'.a₁ * Q (0 : Fin 3) + Q (1 : Fin 3) + W'.a₃ * Q (2 : Fin 3)) * Q (1 : Fin 3)) :=
  by rw [dblAddY];
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
  ring1


-- @@ L214-216 expanded
lemma dblAddZ_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddZ ![0, Y₁, 0] Q =
      Y₁ ^ 2 * ((W'.a₁ * Q (0 : Fin 3) + Q (1 : Fin 3) + W'.a₃ * Q (2 : Fin 3)) * Q (2 : Fin 3)) :=
  by rw [dblAddZ];
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
  ring1


-- @@ L218-220 expanded
lemma dblAddX_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddX P ![0, Y₂, 0] = Y₂ ^ 2 * (P (1 : Fin 3) * P (0 : Fin 3)) := by rw [dblAddX];
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
  ring1


-- @@ L222-224 expanded
lemma dblAddY_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddY P ![0, Y₂, 0] = Y₂ ^ 2 * (P (1 : Fin 3) * P (1 : Fin 3)) := by rw [dblAddY];
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
  ring1


-- @@ L226-228 expanded
lemma dblAddZ_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddZ P ![0, Y₂, 0] = Y₂ ^ 2 * (P (1 : Fin 3) * P (2 : Fin 3)) := by rw [dblAddZ];
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two];
  ring1


-- @@ L230-230 verbatim
/-! ## The diagonal of law 2 is mathlib's doubling -/


-- @@ L232-239 expanded
/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblX`. CAS-certified cofactor (3–13 terms; `cof_diag_dblAddX.txt`). -/
lemma dblAddX_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddX P P = W'.dblX P := by
  linear_combination (norm := (law_simp; ring1))
    (W'.a₁ ^ 3 * P (0 : Fin 3) + 4 * W'.a₁ * W'.a₂ * P (0 : Fin 3) + 9 * W'.a₃ * P (0 : Fin 3) +
              2 * W'.a₁ ^ 2 * P (1 : Fin 3) +
            8 * W'.a₂ * P (1 : Fin 3) +
          W'.a₁ ^ 2 * W'.a₃ * P (2 : Fin 3) +
        4 * W'.a₂ * W'.a₃ * P (2 : Fin 3)) *
      (equation_iff P).mp hP


-- @@ L241-250 expanded
/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblY`. CAS-certified cofactor (`cof_diag_dblAddY.txt`). -/
lemma dblAddY_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddY P P = W'.dblY P := by
  linear_combination (norm := (law_simp; ring1))
    (-W'.a₁ ^ 4 * P (0 : Fin 3) - 6 * W'.a₁ ^ 2 * W'.a₂ * P (0 : Fin 3) -
                            8 * W'.a₂ ^ 2 * P (0 : Fin 3) -
                          3 * W'.a₄ * P (0 : Fin 3) -
                        W'.a₁ ^ 3 * P (1 : Fin 3) -
                      4 * W'.a₁ * W'.a₂ * P (1 : Fin 3) +
                    12 * W'.a₃ * P (1 : Fin 3) -
                  W'.a₁ ^ 3 * W'.a₃ * P (2 : Fin 3) -
                W'.a₁ ^ 2 * W'.a₄ * P (2 : Fin 3) -
              4 * W'.a₁ * W'.a₂ * W'.a₃ * P (2 : Fin 3) -
            4 * W'.a₂ * W'.a₄ * P (2 : Fin 3) +
          6 * W'.a₃ ^ 2 * P (2 : Fin 3) +
        9 * W'.a₆ * P (2 : Fin 3)) *
      (equation_iff P).mp hP


-- @@ L252-258 expanded
/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblZ`. CAS-certified cofactor (`cof_diag_dblAddZ.txt`). -/
lemma dblAddZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddZ P P = W'.dblZ P := by
  linear_combination (norm := (law_simp; ring1))
    (-3 * W'.a₁ * P (0 : Fin 3) - 6 * P (1 : Fin 3) - 3 * W'.a₃ * P (2 : Fin 3)) *
      (equation_iff P).mp hP


-- @@ L260-262 verbatim
/-- On the curve, the diagonal of the second addition law is mathlib's doubling `dblXYZ`. -/
lemma dblAddXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddXYZ P P = W'.dblXYZ P := by
  rw [dblAddXYZ, dblAddX_self hP, dblAddY_self hP, dblAddZ_self hP, dblXYZ]


-- @@ L264-264 verbatim
/-! ## The cross-law minors: the two laws are projectively proportional on the curve -/


-- @@ L266-375 expanded
/-- **(T-W7.0c(c3))** The `XY` minor of the two addition laws vanishes on the curve:
law 1 and law 2 are projectively proportional wherever both are defined. CAS-certified
cofactors (Y-first reduction; see `scripts/tw7-p1-bosma-lenstra/cof_MXY_P.txt`, `_Q.txt`). -/
lemma addX_mul_dblAddY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * W'.dblAddY P Q = W'.addY P Q * W'.dblAddX P Q := by
  linear_combination (norm := (law_simp; ring1))
    (-W'.a₁ ^ 2 * W'.a₂ * P (0 : Fin 3) * Q (0 : Fin 3) ^ 4 +
                                                                                                                                                                                                                                  3 *
                                                                                                                                                                                                                                          W'.a₁ *
                                                                                                                                                                                                                                        W'.a₃ *
                                                                                                                                                                                                                                      P
                                                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                                                          Fin
                                                                                                                                                                                                                                            3) *
                                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                                                          Fin
                                                                                                                                                                                                                                            3) ^
                                                                                                                                                                                                                                      4 -
                                                                                                                                                                                                                                W'.a₂ ^
                                                                                                                                                                                                                                      2 *
                                                                                                                                                                                                                                    P
                                                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                                                        Fin
                                                                                                                                                                                                                                          3) *
                                                                                                                                                                                                                                  Q
                                                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                                                        Fin
                                                                                                                                                                                                                                          3) ^
                                                                                                                                                                                                                                    4 -
                                                                                                                                                                                                                              3 *
                                                                                                                                                                                                                                    W'.a₄ *
                                                                                                                                                                                                                                  P
                                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                                        3) *
                                                                                                                                                                                                                                Q
                                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                                                  4 -
                                                                                                                                                                                                                            3 *
                                                                                                                                                                                                                                      W'.a₁ *
                                                                                                                                                                                                                                    W'.a₂ *
                                                                                                                                                                                                                                  P
                                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                                        3) *
                                                                                                                                                                                                                                Q
                                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                                                  3 *
                                                                                                                                                                                                                              Q
                                                                                                                                                                                                                                (1 :
                                                                                                                                                                                                                                  Fin
                                                                                                                                                                                                                                    3) +
                                                                                                                                                                                                                          3 *
                                                                                                                                                                                                                                  W'.a₃ *
                                                                                                                                                                                                                                P
                                                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                                                    Fin
                                                                                                                                                                                                                                      3) *
                                                                                                                                                                                                                              Q
                                                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                                                    Fin
                                                                                                                                                                                                                                      3) ^
                                                                                                                                                                                                                                3 *
                                                                                                                                                                                                                            Q
                                                                                                                                                                                                                              (1 :
                                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                                  3) -
                                                                                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                                                                                  3 *
                                                                                                                                                                                                                                W'.a₃ *
                                                                                                                                                                                                                              P
                                                                                                                                                                                                                                (0 :
                                                                                                                                                                                                                                  Fin
                                                                                                                                                                                                                                    3) *
                                                                                                                                                                                                                            Q
                                                                                                                                                                                                                                (0 :
                                                                                                                                                                                                                                  Fin
                                                                                                                                                                                                                                    3) ^
                                                                                                                                                                                                                              3 *
                                                                                                                                                                                                                          Q
                                                                                                                                                                                                                            (2 :
                                                                                                                                                                                                                              Fin
                                                                                                                                                                                                                                3) -
                                                                                                                                                                                                                      W'.a₁ ^
                                                                                                                                                                                                                                2 *
                                                                                                                                                                                                                              W'.a₄ *
                                                                                                                                                                                                                            P
                                                                                                                                                                                                                              (0 :
                                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                                  3) *
                                                                                                                                                                                                                          Q
                                                                                                                                                                                                                              (0 :
                                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                                  3) ^
                                                                                                                                                                                                                            3 *
                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                          (2 :
                                                                                                                                                                                                                            Fin
                                                                                                                                                                                                                              3) -
                                                                                                                                                                                                                    W'.a₁ *
                                                                                                                                                                                                                              W'.a₂ *
                                                                                                                                                                                                                            W'.a₃ *
                                                                                                                                                                                                                          P
                                                                                                                                                                                                                            (0 :
                                                                                                                                                                                                                              Fin
                                                                                                                                                                                                                                3) *
                                                                                                                                                                                                                        Q
                                                                                                                                                                                                                            (0 :
                                                                                                                                                                                                                              Fin
                                                                                                                                                                                                                                3) ^
                                                                                                                                                                                                                          3 *
                                                                                                                                                                                                                      Q
                                                                                                                                                                                                                        (2 :
                                                                                                                                                                                                                          Fin
                                                                                                                                                                                                                            3) -
                                                                                                                                                                                                                  7 *
                                                                                                                                                                                                                            W'.a₂ *
                                                                                                                                                                                                                          W'.a₄ *
                                                                                                                                                                                                                        P
                                                                                                                                                                                                                          (0 :
                                                                                                                                                                                                                            Fin
                                                                                                                                                                                                                              3) *
                                                                                                                                                                                                                      Q
                                                                                                                                                                                                                          (0 :
                                                                                                                                                                                                                            Fin
                                                                                                                                                                                                                              3) ^
                                                                                                                                                                                                                        3 *
                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                      (2 :
                                                                                                                                                                                                                        Fin
                                                                                                                                                                                                                          3) -
                                                                                                                                                                                                                3 *
                                                                                                                                                                                                                        W'.a₃ ^
                                                                                                                                                                                                                          2 *
                                                                                                                                                                                                                      P
                                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                                          Fin
                                                                                                                                                                                                                            3) *
                                                                                                                                                                                                                    Q
                                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                                          Fin
                                                                                                                                                                                                                            3) ^
                                                                                                                                                                                                                      3 *
                                                                                                                                                                                                                  Q
                                                                                                                                                                                                                    (2 :
                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                        3) -
                                                                                                                                                                                                              9 *
                                                                                                                                                                                                                      W'.a₆ *
                                                                                                                                                                                                                    P
                                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                                        Fin
                                                                                                                                                                                                                          3) *
                                                                                                                                                                                                                  Q
                                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                                        Fin
                                                                                                                                                                                                                          3) ^
                                                                                                                                                                                                                    3 *
                                                                                                                                                                                                                Q
                                                                                                                                                                                                                  (2 :
                                                                                                                                                                                                                    Fin
                                                                                                                                                                                                                      3) -
                                                                                                                                                                                                            3 *
                                                                                                                                                                                                                    W'.a₂ *
                                                                                                                                                                                                                  P
                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                        3) *
                                                                                                                                                                                                                Q
                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                                  2 *
                                                                                                                                                                                                              Q
                                                                                                                                                                                                                  (1 :
                                                                                                                                                                                                                    Fin
                                                                                                                                                                                                                      3) ^
                                                                                                                                                                                                                2 -
                                                                                                                                                                                                          6 *
                                                                                                                                                                                                                      W'.a₁ ^
                                                                                                                                                                                                                        2 *
                                                                                                                                                                                                                    W'.a₃ *
                                                                                                                                                                                                                  P
                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                        3) *
                                                                                                                                                                                                                Q
                                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                                      Fin
                                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                                  2 *
                                                                                                                                                                                                              Q
                                                                                                                                                                                                                (1 :
                                                                                                                                                                                                                  Fin
                                                                                                                                                                                                                    3) *
                                                                                                                                                                                                            Q
                                                                                                                                                                                                              (2 :
                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                  3) -
                                                                                                                                                                                                        3 *
                                                                                                                                                                                                                  W'.a₁ ^
                                                                                                                                                                                                                    2 *
                                                                                                                                                                                                                W'.a₃ ^
                                                                                                                                                                                                                  2 *
                                                                                                                                                                                                              P
                                                                                                                                                                                                                (0 :
                                                                                                                                                                                                                  Fin
                                                                                                                                                                                                                    3) *
                                                                                                                                                                                                            Q
                                                                                                                                                                                                                (0 :
                                                                                                                                                                                                                  Fin
                                                                                                                                                                                                                    3) ^
                                                                                                                                                                                                              2 *
                                                                                                                                                                                                          Q
                                                                                                                                                                                                              (2 :
                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                  3) ^
                                                                                                                                                                                                            2 -
                                                                                                                                                                                                      3 *
                                                                                                                                                                                                                  W'.a₁ *
                                                                                                                                                                                                                W'.a₃ *
                                                                                                                                                                                                              W'.a₄ *
                                                                                                                                                                                                            P
                                                                                                                                                                                                              (0 :
                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                  3) *
                                                                                                                                                                                                          Q
                                                                                                                                                                                                              (0 :
                                                                                                                                                                                                                Fin
                                                                                                                                                                                                                  3) ^
                                                                                                                                                                                                            2 *
                                                                                                                                                                                                        Q
                                                                                                                                                                                                            (2 :
                                                                                                                                                                                                              Fin
                                                                                                                                                                                                                3) ^
                                                                                                                                                                                                          2 -
                                                                                                                                                                                                    6 *
                                                                                                                                                                                                              W'.a₂ *
                                                                                                                                                                                                            W'.a₃ ^
                                                                                                                                                                                                              2 *
                                                                                                                                                                                                          P
                                                                                                                                                                                                            (0 :
                                                                                                                                                                                                              Fin
                                                                                                                                                                                                                3) *
                                                                                                                                                                                                        Q
                                                                                                                                                                                                            (0 :
                                                                                                                                                                                                              Fin
                                                                                                                                                                                                                3) ^
                                                                                                                                                                                                          2 *
                                                                                                                                                                                                      Q
                                                                                                                                                                                                          (2 :
                                                                                                                                                                                                            Fin
                                                                                                                                                                                                              3) ^
                                                                                                                                                                                                        2 -
                                                                                                                                                                                                  18 *
                                                                                                                                                                                                            W'.a₂ *
                                                                                                                                                                                                          W'.a₆ *
                                                                                                                                                                                                        P
                                                                                                                                                                                                          (0 :
                                                                                                                                                                                                            Fin
                                                                                                                                                                                                              3) *
                                                                                                                                                                                                      Q
                                                                                                                                                                                                          (0 :
                                                                                                                                                                                                            Fin
                                                                                                                                                                                                              3) ^
                                                                                                                                                                                                        2 *
                                                                                                                                                                                                    Q
                                                                                                                                                                                                        (2 :
                                                                                                                                                                                                          Fin
                                                                                                                                                                                                            3) ^
                                                                                                                                                                                                      2 -
                                                                                                                                                                                                6 *
                                                                                                                                                                                                        W'.a₄ ^
                                                                                                                                                                                                          2 *
                                                                                                                                                                                                      P
                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                          Fin
                                                                                                                                                                                                            3) *
                                                                                                                                                                                                    Q
                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                          Fin
                                                                                                                                                                                                            3) ^
                                                                                                                                                                                                      2 *
                                                                                                                                                                                                  Q
                                                                                                                                                                                                      (2 :
                                                                                                                                                                                                        Fin
                                                                                                                                                                                                          3) ^
                                                                                                                                                                                                    2 -
                                                                                                                                                                                              9 *
                                                                                                                                                                                                          W'.a₁ *
                                                                                                                                                                                                        W'.a₃ *
                                                                                                                                                                                                      P
                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                          Fin
                                                                                                                                                                                                            3) *
                                                                                                                                                                                                    Q
                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                        Fin
                                                                                                                                                                                                          3) *
                                                                                                                                                                                                  Q
                                                                                                                                                                                                      (1 :
                                                                                                                                                                                                        Fin
                                                                                                                                                                                                          3) ^
                                                                                                                                                                                                    2 *
                                                                                                                                                                                                Q
                                                                                                                                                                                                  (2 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) -
                                                                                                                                                                                            3 *
                                                                                                                                                                                                        W'.a₁ *
                                                                                                                                                                                                      W'.a₃ ^
                                                                                                                                                                                                        2 *
                                                                                                                                                                                                    P
                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                        Fin
                                                                                                                                                                                                          3) *
                                                                                                                                                                                                  Q
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) *
                                                                                                                                                                                                Q
                                                                                                                                                                                                  (1 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) *
                                                                                                                                                                                              Q
                                                                                                                                                                                                  (2 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) ^
                                                                                                                                                                                                2 +
                                                                                                                                                                                          9 *
                                                                                                                                                                                                      W'.a₁ *
                                                                                                                                                                                                    W'.a₆ *
                                                                                                                                                                                                  P
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) *
                                                                                                                                                                                                Q
                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) *
                                                                                                                                                                                              Q
                                                                                                                                                                                                (1 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) *
                                                                                                                                                                                            Q
                                                                                                                                                                                                (2 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) ^
                                                                                                                                                                                              2 +
                                                                                                                                                                                        3 *
                                                                                                                                                                                                    W'.a₃ *
                                                                                                                                                                                                  W'.a₄ *
                                                                                                                                                                                                P
                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) *
                                                                                                                                                                                              Q
                                                                                                                                                                                                (0 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) *
                                                                                                                                                                                            Q
                                                                                                                                                                                              (1 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) *
                                                                                                                                                                                          Q
                                                                                                                                                                                              (2 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) ^
                                                                                                                                                                                            2 -
                                                                                                                                                                                      W'.a₁ ^
                                                                                                                                                                                                  2 *
                                                                                                                                                                                                W'.a₂ *
                                                                                                                                                                                              W'.a₆ *
                                                                                                                                                                                            P
                                                                                                                                                                                              (0 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) *
                                                                                                                                                                                          Q
                                                                                                                                                                                            (0 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) *
                                                                                                                                                                                        Q
                                                                                                                                                                                            (2 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) ^
                                                                                                                                                                                          3 +
                                                                                                                                                                                    W'.a₁ *
                                                                                                                                                                                                W'.a₂ *
                                                                                                                                                                                              W'.a₃ *
                                                                                                                                                                                            W'.a₄ *
                                                                                                                                                                                          P
                                                                                                                                                                                            (0 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) *
                                                                                                                                                                                        Q
                                                                                                                                                                                          (0 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) *
                                                                                                                                                                                      Q
                                                                                                                                                                                          (2 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) ^
                                                                                                                                                                                        3 -
                                                                                                                                                                                  3 *
                                                                                                                                                                                            W'.a₁ *
                                                                                                                                                                                          W'.a₃ ^
                                                                                                                                                                                            3 *
                                                                                                                                                                                        P
                                                                                                                                                                                          (0 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) *
                                                                                                                                                                                      Q
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) *
                                                                                                                                                                                    Q
                                                                                                                                                                                        (2 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) ^
                                                                                                                                                                                      3 -
                                                                                                                                                                                6 *
                                                                                                                                                                                            W'.a₁ *
                                                                                                                                                                                          W'.a₃ *
                                                                                                                                                                                        W'.a₆ *
                                                                                                                                                                                      P
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) *
                                                                                                                                                                                    Q
                                                                                                                                                                                      (0 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) *
                                                                                                                                                                                  Q
                                                                                                                                                                                      (2 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) ^
                                                                                                                                                                                    3 -
                                                                                                                                                                              W'.a₂ ^
                                                                                                                                                                                        2 *
                                                                                                                                                                                      W'.a₃ ^
                                                                                                                                                                                        2 *
                                                                                                                                                                                    P
                                                                                                                                                                                      (0 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) *
                                                                                                                                                                                  Q
                                                                                                                                                                                    (0 :
                                                                                                                                                                                      Fin
                                                                                                                                                                                        3) *
                                                                                                                                                                                Q
                                                                                                                                                                                    (2 :
                                                                                                                                                                                      Fin
                                                                                                                                                                                        3) ^
                                                                                                                                                                                  3 -
                                                                                                                                                                            4 *
                                                                                                                                                                                      W'.a₂ ^
                                                                                                                                                                                        2 *
                                                                                                                                                                                    W'.a₆ *
                                                                                                                                                                                  P
                                                                                                                                                                                    (0 :
                                                                                                                                                                                      Fin
                                                                                                                                                                                        3) *
                                                                                                                                                                                Q
                                                                                                                                                                                  (0 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) *
                                                                                                                                                                              Q
                                                                                                                                                                                  (2 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) ^
                                                                                                                                                                                3 +
                                                                                                                                                                          W'.a₂ *
                                                                                                                                                                                  W'.a₄ ^
                                                                                                                                                                                    2 *
                                                                                                                                                                                P
                                                                                                                                                                                  (0 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) *
                                                                                                                                                                              Q
                                                                                                                                                                                (0 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) *
                                                                                                                                                                            Q
                                                                                                                                                                                (2 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) ^
                                                                                                                                                                              3 -
                                                                                                                                                                        6 *
                                                                                                                                                                                  W'.a₃ ^
                                                                                                                                                                                    2 *
                                                                                                                                                                                W'.a₄ *
                                                                                                                                                                              P
                                                                                                                                                                                (0 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) *
                                                                                                                                                                            Q
                                                                                                                                                                              (0 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) *
                                                                                                                                                                          Q
                                                                                                                                                                              (2 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) ^
                                                                                                                                                                            3 -
                                                                                                                                                                      21 *
                                                                                                                                                                                W'.a₄ *
                                                                                                                                                                              W'.a₆ *
                                                                                                                                                                            P
                                                                                                                                                                              (0 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) *
                                                                                                                                                                          Q
                                                                                                                                                                            (0 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) *
                                                                                                                                                                        Q
                                                                                                                                                                            (2 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) ^
                                                                                                                                                                          3 -
                                                                                                                                                                    3 *
                                                                                                                                                                            W'.a₃ *
                                                                                                                                                                          P
                                                                                                                                                                            (0 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) *
                                                                                                                                                                        Q
                                                                                                                                                                            (1 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) ^
                                                                                                                                                                          3 *
                                                                                                                                                                      Q
                                                                                                                                                                        (2 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) +
                                                                                                                                                                  9 *
                                                                                                                                                                          W'.a₆ *
                                                                                                                                                                        P
                                                                                                                                                                          (0 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) *
                                                                                                                                                                      Q
                                                                                                                                                                          (1 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) ^
                                                                                                                                                                        2 *
                                                                                                                                                                    Q
                                                                                                                                                                        (2 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) ^
                                                                                                                                                                      2 +
                                                                                                                                                                3 *
                                                                                                                                                                        W'.a₃ ^
                                                                                                                                                                          3 *
                                                                                                                                                                      P
                                                                                                                                                                        (0 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) *
                                                                                                                                                                    Q
                                                                                                                                                                      (1 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) *
                                                                                                                                                                  Q
                                                                                                                                                                      (2 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) ^
                                                                                                                                                                    3 +
                                                                                                                                                              12 *
                                                                                                                                                                        W'.a₃ *
                                                                                                                                                                      W'.a₆ *
                                                                                                                                                                    P
                                                                                                                                                                      (0 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) *
                                                                                                                                                                  Q
                                                                                                                                                                    (1 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) *
                                                                                                                                                                Q
                                                                                                                                                                    (2 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) ^
                                                                                                                                                                  3 -
                                                                                                                                                            W'.a₁ ^
                                                                                                                                                                      3 *
                                                                                                                                                                    W'.a₃ *
                                                                                                                                                                  W'.a₆ *
                                                                                                                                                                P
                                                                                                                                                                  (0 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) *
                                                                                                                                                              Q
                                                                                                                                                                  (2 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) ^
                                                                                                                                                                4 +
                                                                                                                                                          W'.a₁ ^
                                                                                                                                                                    2 *
                                                                                                                                                                  W'.a₃ ^
                                                                                                                                                                    2 *
                                                                                                                                                                W'.a₄ *
                                                                                                                                                              P
                                                                                                                                                                (0 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) *
                                                                                                                                                            Q
                                                                                                                                                                (2 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) ^
                                                                                                                                                              4 -
                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                  2 *
                                                                                                                                                                W'.a₄ *
                                                                                                                                                              W'.a₆ *
                                                                                                                                                            P
                                                                                                                                                              (0 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) *
                                                                                                                                                          Q
                                                                                                                                                              (2 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) ^
                                                                                                                                                            4 -
                                                                                                                                                      W'.a₁ *
                                                                                                                                                              W'.a₂ *
                                                                                                                                                            W'.a₃ ^
                                                                                                                                                              3 *
                                                                                                                                                          P
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) *
                                                                                                                                                        Q
                                                                                                                                                            (2 :
                                                                                                                                                              Fin
                                                                                                                                                                3) ^
                                                                                                                                                          4 -
                                                                                                                                                    4 *
                                                                                                                                                                W'.a₁ *
                                                                                                                                                              W'.a₂ *
                                                                                                                                                            W'.a₃ *
                                                                                                                                                          W'.a₆ *
                                                                                                                                                        P
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) *
                                                                                                                                                      Q
                                                                                                                                                          (2 :
                                                                                                                                                            Fin
                                                                                                                                                              3) ^
                                                                                                                                                        4 +
                                                                                                                                                  2 *
                                                                                                                                                            W'.a₁ *
                                                                                                                                                          W'.a₃ *
                                                                                                                                                        W'.a₄ ^
                                                                                                                                                          2 *
                                                                                                                                                      P
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) *
                                                                                                                                                    Q
                                                                                                                                                        (2 :
                                                                                                                                                          Fin
                                                                                                                                                            3) ^
                                                                                                                                                      4 -
                                                                                                                                                W'.a₂ *
                                                                                                                                                        W'.a₃ ^
                                                                                                                                                          2 *
                                                                                                                                                      W'.a₄ *
                                                                                                                                                    P
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) *
                                                                                                                                                  Q
                                                                                                                                                      (2 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    4 -
                                                                                                                                              4 *
                                                                                                                                                        W'.a₂ *
                                                                                                                                                      W'.a₄ *
                                                                                                                                                    W'.a₆ *
                                                                                                                                                  P
                                                                                                                                                    (0 :
                                                                                                                                                      Fin
                                                                                                                                                        3) *
                                                                                                                                                Q
                                                                                                                                                    (2 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  4 -
                                                                                                                                            3 *
                                                                                                                                                    W'.a₃ ^
                                                                                                                                                      2 *
                                                                                                                                                  W'.a₆ *
                                                                                                                                                P
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) *
                                                                                                                                              Q
                                                                                                                                                  (2 :
                                                                                                                                                    Fin
                                                                                                                                                      3) ^
                                                                                                                                                4 +
                                                                                                                                          W'.a₄ ^
                                                                                                                                                3 *
                                                                                                                                              P
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) *
                                                                                                                                            Q
                                                                                                                                                (2 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              4 -
                                                                                                                                        9 *
                                                                                                                                              W'.a₆ ^
                                                                                                                                                2 *
                                                                                                                                            P
                                                                                                                                              (0 :
                                                                                                                                                Fin
                                                                                                                                                  3) *
                                                                                                                                          Q
                                                                                                                                              (2 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            4 +
                                                                                                                                      W'.a₁ ^
                                                                                                                                            3 *
                                                                                                                                          P
                                                                                                                                            (1 :
                                                                                                                                              Fin
                                                                                                                                                3) *
                                                                                                                                        Q
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          4 +
                                                                                                                                    W'.a₁ *
                                                                                                                                          W'.a₂ *
                                                                                                                                        P
                                                                                                                                          (1 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      Q
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        4 +
                                                                                                                                  4 *
                                                                                                                                          W'.a₁ ^
                                                                                                                                            2 *
                                                                                                                                        P
                                                                                                                                          (1 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      Q
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        3 *
                                                                                                                                    Q
                                                                                                                                      (1 :
                                                                                                                                        Fin
                                                                                                                                          3) +
                                                                                                                                W'.a₂ *
                                                                                                                                      P
                                                                                                                                        (1 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    Q
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      3 *
                                                                                                                                  Q
                                                                                                                                    (1 :
                                                                                                                                      Fin
                                                                                                                                        3) +
                                                                                                                              3 *
                                                                                                                                        W'.a₁ ^
                                                                                                                                          2 *
                                                                                                                                      W'.a₃ *
                                                                                                                                    P
                                                                                                                                      (1 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  Q
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) ^
                                                                                                                                    3 *
                                                                                                                                Q
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) +
                                                                                                                            3 *
                                                                                                                                      W'.a₁ *
                                                                                                                                    W'.a₄ *
                                                                                                                                  P
                                                                                                                                    (1 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                Q
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) ^
                                                                                                                                  3 *
                                                                                                                              Q
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) +
                                                                                                                          6 *
                                                                                                                                  W'.a₁ *
                                                                                                                                P
                                                                                                                                  (1 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 *
                                                                                                                            Q
                                                                                                                                (1 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 +
                                                                                                                        6 *
                                                                                                                                    W'.a₁ *
                                                                                                                                  W'.a₃ *
                                                                                                                                P
                                                                                                                                  (1 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 *
                                                                                                                            Q
                                                                                                                              (1 :
                                                                                                                                Fin
                                                                                                                                  3) *
                                                                                                                          Q
                                                                                                                            (2 :
                                                                                                                              Fin
                                                                                                                                3) +
                                                                                                                      3 *
                                                                                                                                W'.a₄ *
                                                                                                                              P
                                                                                                                                (1 :
                                                                                                                                  Fin
                                                                                                                                    3) *
                                                                                                                            Q
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 *
                                                                                                                          Q
                                                                                                                            (1 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        Q
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) +
                                                                                                                    3 *
                                                                                                                              W'.a₁ *
                                                                                                                            W'.a₃ ^
                                                                                                                              2 *
                                                                                                                          P
                                                                                                                            (1 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        Q
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 *
                                                                                                                      Q
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 +
                                                                                                                  9 *
                                                                                                                            W'.a₁ *
                                                                                                                          W'.a₆ *
                                                                                                                        P
                                                                                                                          (1 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      Q
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 *
                                                                                                                    Q
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 +
                                                                                                                3 *
                                                                                                                      P
                                                                                                                        (1 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                      (1 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    3 +
                                                                                                              3 *
                                                                                                                        W'.a₃ *
                                                                                                                      P
                                                                                                                        (1 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                      (1 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    2 *
                                                                                                                Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) +
                                                                                                            3 *
                                                                                                                      W'.a₃ ^
                                                                                                                        2 *
                                                                                                                    P
                                                                                                                      (1 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (1 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                2 +
                                                                                                          9 *
                                                                                                                    W'.a₆ *
                                                                                                                  P
                                                                                                                    (1 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              2 +
                                                                                                        W'.a₁ ^
                                                                                                                  3 *
                                                                                                                W'.a₆ *
                                                                                                              P
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            3 -
                                                                                                      W'.a₁ ^
                                                                                                                  2 *
                                                                                                                W'.a₃ *
                                                                                                              W'.a₄ *
                                                                                                            P
                                                                                                              (1 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        Q
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          3 +
                                                                                                    W'.a₁ *
                                                                                                              W'.a₂ *
                                                                                                            W'.a₃ ^
                                                                                                              2 *
                                                                                                          P
                                                                                                            (1 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        Q
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        3 +
                                                                                                  4 *
                                                                                                              W'.a₁ *
                                                                                                            W'.a₂ *
                                                                                                          W'.a₆ *
                                                                                                        P
                                                                                                          (1 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      Q
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      3 -
                                                                                                W'.a₁ *
                                                                                                        W'.a₄ ^
                                                                                                          2 *
                                                                                                      P
                                                                                                        (1 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    3 +
                                                                                              W'.a₁ ^
                                                                                                        2 *
                                                                                                      W'.a₆ *
                                                                                                    P
                                                                                                      (1 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                    (1 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  3 -
                                                                                            W'.a₁ *
                                                                                                      W'.a₃ *
                                                                                                    W'.a₄ *
                                                                                                  P
                                                                                                    (1 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                  (1 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              Q
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                3 +
                                                                                          W'.a₂ *
                                                                                                  W'.a₃ ^
                                                                                                    2 *
                                                                                                P
                                                                                                  (1 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              Q
                                                                                                (1 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              3 +
                                                                                        4 * W'.a₂ *
                                                                                                W'.a₆ *
                                                                                              P
                                                                                                (1 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            3 -
                                                                                      W'.a₄ ^ 2 *
                                                                                            P
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                            (1 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          3 -
                                                                                    W'.a₁ ^ 2 *
                                                                                          W'.a₄ *
                                                                                        P
                                                                                          (2 :
                                                                                            Fin 3) *
                                                                                      Q
                                                                                          (0 :
                                                                                            Fin 3) ^
                                                                                        4 -
                                                                                  W'.a₂ * W'.a₄ *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) ^
                                                                                      4 -
                                                                                3 * W'.a₁ * W'.a₄ *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) ^
                                                                                      3 *
                                                                                  Q (1 : Fin 3) -
                                                                              W'.a₁ ^ 2 *
                                                                                      W'.a₃ ^ 2 *
                                                                                    P (2 : Fin 3) *
                                                                                  Q (0 : Fin 3) ^
                                                                                    3 *
                                                                                Q (2 : Fin 3) -
                                                                            3 * W'.a₁ ^ 2 * W'.a₆ *
                                                                                  P (2 : Fin 3) *
                                                                                Q (0 : Fin 3) ^ 3 *
                                                                              Q (2 : Fin 3) -
                                                                          3 * W'.a₁ * W'.a₃ *
                                                                                  W'.a₄ *
                                                                                P (2 : Fin 3) *
                                                                              Q (0 : Fin 3) ^ 3 *
                                                                            Q (2 : Fin 3) -
                                                                        W'.a₂ * W'.a₃ ^ 2 *
                                                                              P (2 : Fin 3) *
                                                                            Q (0 : Fin 3) ^ 3 *
                                                                          Q (2 : Fin 3) -
                                                                      3 * W'.a₂ * W'.a₆ *
                                                                            P (2 : Fin 3) *
                                                                          Q (0 : Fin 3) ^ 3 *
                                                                        Q (2 : Fin 3) -
                                                                    3 * W'.a₄ ^ 2 * P (2 : Fin 3) *
                                                                        Q (0 : Fin 3) ^ 3 *
                                                                      Q (2 : Fin 3) -
                                                                  3 * W'.a₄ * P (2 : Fin 3) *
                                                                      Q (0 : Fin 3) ^ 2 *
                                                                    Q (1 : Fin 3) ^ 2 -
                                                                3 * W'.a₁ * W'.a₃ ^ 2 *
                                                                        P (2 : Fin 3) *
                                                                      Q (0 : Fin 3) ^ 2 *
                                                                    Q (1 : Fin 3) *
                                                                  Q (2 : Fin 3) -
                                                              9 * W'.a₁ * W'.a₆ * P (2 : Fin 3) *
                                                                    Q (0 : Fin 3) ^ 2 *
                                                                  Q (1 : Fin 3) *
                                                                Q (2 : Fin 3) -
                                                            3 * W'.a₃ * W'.a₄ * P (2 : Fin 3) *
                                                                  Q (0 : Fin 3) ^ 2 *
                                                                Q (1 : Fin 3) *
                                                              Q (2 : Fin 3) -
                                                          3 * W'.a₁ * W'.a₃ ^ 3 * P (2 : Fin 3) *
                                                              Q (0 : Fin 3) ^ 2 *
                                                            Q (2 : Fin 3) ^ 2 -
                                                        9 * W'.a₁ * W'.a₃ * W'.a₆ * P (2 : Fin 3) *
                                                            Q (0 : Fin 3) ^ 2 *
                                                          Q (2 : Fin 3) ^ 2 -
                                                      6 * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) *
                                                          Q (0 : Fin 3) ^ 2 *
                                                        Q (2 : Fin 3) ^ 2 -
                                                    18 * W'.a₄ * W'.a₆ * P (2 : Fin 3) *
                                                        Q (0 : Fin 3) ^ 2 *
                                                      Q (2 : Fin 3) ^ 2 -
                                                  3 * W'.a₃ ^ 2 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                                      Q (1 : Fin 3) ^ 2 *
                                                    Q (2 : Fin 3) -
                                                9 * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                                    Q (1 : Fin 3) ^ 2 *
                                                  Q (2 : Fin 3) -
                                              3 * W'.a₃ ^ 3 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                                  Q (1 : Fin 3) *
                                                Q (2 : Fin 3) ^ 2 -
                                            9 * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                                Q (1 : Fin 3) *
                                              Q (2 : Fin 3) ^ 2 -
                                          W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P (2 : Fin 3) *
                                              Q (0 : Fin 3) *
                                            Q (2 : Fin 3) ^ 3 +
                                        W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                          Q (2 : Fin 3) ^ 3 -
                                      W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                        Q (2 : Fin 3) ^ 3 -
                                    4 * W'.a₂ * W'.a₄ * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                      Q (2 : Fin 3) ^ 3 -
                                  3 * W'.a₃ ^ 4 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                    Q (2 : Fin 3) ^ 3 -
                                18 * W'.a₃ ^ 2 * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                  Q (2 : Fin 3) ^ 3 +
                              W'.a₄ ^ 3 * P (2 : Fin 3) * Q (0 : Fin 3) * Q (2 : Fin 3) ^ 3 -
                            27 * W'.a₆ ^ 2 * P (2 : Fin 3) * Q (0 : Fin 3) * Q (2 : Fin 3) ^ 3 -
                          W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                        3 * W'.a₁ ^ 2 * W'.a₆ ^ 2 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
                      W'.a₁ * W'.a₃ ^ 3 * W'.a₄ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
                    3 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                  W'.a₂ * W'.a₃ ^ 4 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                7 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
              12 * W'.a₂ * W'.a₆ ^ 2 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
            W'.a₃ ^ 2 * W'.a₄ ^ 2 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
          3 * W'.a₄ ^ 2 * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4) *
        (equation_iff P).mp hP +
      (W'.a₁ ^ 2 * W'.a₂ * P (0 : Fin 3) ^ 4 * Q (0 : Fin 3) -
                                                                                                                                                                                                3 *
                                                                                                                                                                                                        W'.a₁ *
                                                                                                                                                                                                      W'.a₃ *
                                                                                                                                                                                                    P
                                                                                                                                                                                                        (0 :
                                                                                                                                                                                                          Fin
                                                                                                                                                                                                            3) ^
                                                                                                                                                                                                      4 *
                                                                                                                                                                                                  Q
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) +
                                                                                                                                                                                              W'.a₂ ^
                                                                                                                                                                                                    2 *
                                                                                                                                                                                                  P
                                                                                                                                                                                                      (0 :
                                                                                                                                                                                                        Fin
                                                                                                                                                                                                          3) ^
                                                                                                                                                                                                    4 *
                                                                                                                                                                                                Q
                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) +
                                                                                                                                                                                            3 *
                                                                                                                                                                                                  W'.a₄ *
                                                                                                                                                                                                P
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                  4 *
                                                                                                                                                                                              Q
                                                                                                                                                                                                (0 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) -
                                                                                                                                                                                          3 *
                                                                                                                                                                                                W'.a₃ *
                                                                                                                                                                                              P
                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) ^
                                                                                                                                                                                                4 *
                                                                                                                                                                                            Q
                                                                                                                                                                                              (1 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) +
                                                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                                                3 *
                                                                                                                                                                                              W'.a₃ *
                                                                                                                                                                                            P
                                                                                                                                                                                                (0 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) ^
                                                                                                                                                                                              4 *
                                                                                                                                                                                          Q
                                                                                                                                                                                            (2 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) +
                                                                                                                                                                                      W'.a₁ ^
                                                                                                                                                                                              2 *
                                                                                                                                                                                            W'.a₄ *
                                                                                                                                                                                          P
                                                                                                                                                                                              (0 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) ^
                                                                                                                                                                                            4 *
                                                                                                                                                                                        Q
                                                                                                                                                                                          (2 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) +
                                                                                                                                                                                    W'.a₁ *
                                                                                                                                                                                            W'.a₂ *
                                                                                                                                                                                          W'.a₃ *
                                                                                                                                                                                        P
                                                                                                                                                                                            (0 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) ^
                                                                                                                                                                                          4 *
                                                                                                                                                                                      Q
                                                                                                                                                                                        (2 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) +
                                                                                                                                                                                  W'.a₂ *
                                                                                                                                                                                        W'.a₄ *
                                                                                                                                                                                      P
                                                                                                                                                                                          (0 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) ^
                                                                                                                                                                                        4 *
                                                                                                                                                                                    Q
                                                                                                                                                                                      (2 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) +
                                                                                                                                                                                3 *
                                                                                                                                                                                      W'.a₃ ^
                                                                                                                                                                                        2 *
                                                                                                                                                                                    P
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) ^
                                                                                                                                                                                      4 *
                                                                                                                                                                                  Q
                                                                                                                                                                                    (2 :
                                                                                                                                                                                      Fin
                                                                                                                                                                                        3) +
                                                                                                                                                                              9 *
                                                                                                                                                                                    W'.a₆ *
                                                                                                                                                                                  P
                                                                                                                                                                                      (0 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) ^
                                                                                                                                                                                    4 *
                                                                                                                                                                                Q
                                                                                                                                                                                  (2 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) -
                                                                                                                                                                            W'.a₁ ^
                                                                                                                                                                                    3 *
                                                                                                                                                                                  P
                                                                                                                                                                                      (0 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) ^
                                                                                                                                                                                    3 *
                                                                                                                                                                                P
                                                                                                                                                                                  (1 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) *
                                                                                                                                                                              Q
                                                                                                                                                                                (0 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) +
                                                                                                                                                                          2 *
                                                                                                                                                                                    W'.a₁ *
                                                                                                                                                                                  W'.a₂ *
                                                                                                                                                                                P
                                                                                                                                                                                    (0 :
                                                                                                                                                                                      Fin
                                                                                                                                                                                        3) ^
                                                                                                                                                                                  3 *
                                                                                                                                                                              P
                                                                                                                                                                                (1 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) *
                                                                                                                                                                            Q
                                                                                                                                                                              (0 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) -
                                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                                2 *
                                                                                                                                                                              P
                                                                                                                                                                                  (0 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) ^
                                                                                                                                                                                3 *
                                                                                                                                                                            P
                                                                                                                                                                              (1 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) *
                                                                                                                                                                          Q
                                                                                                                                                                            (1 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) -
                                                                                                                                                                      W'.a₂ *
                                                                                                                                                                            P
                                                                                                                                                                                (0 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) ^
                                                                                                                                                                              3 *
                                                                                                                                                                          P
                                                                                                                                                                            (1 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) *
                                                                                                                                                                        Q
                                                                                                                                                                          (1 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) +
                                                                                                                                                                    3 *
                                                                                                                                                                              W'.a₁ ^
                                                                                                                                                                                2 *
                                                                                                                                                                            W'.a₃ *
                                                                                                                                                                          P
                                                                                                                                                                              (0 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) ^
                                                                                                                                                                            3 *
                                                                                                                                                                        P
                                                                                                                                                                          (1 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) *
                                                                                                                                                                      Q
                                                                                                                                                                        (2 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) +
                                                                                                                                                                  3 *
                                                                                                                                                                            W'.a₁ *
                                                                                                                                                                          W'.a₄ *
                                                                                                                                                                        P
                                                                                                                                                                            (0 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) ^
                                                                                                                                                                          3 *
                                                                                                                                                                      P
                                                                                                                                                                        (1 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) *
                                                                                                                                                                    Q
                                                                                                                                                                      (2 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) +
                                                                                                                                                                W'.a₁ ^
                                                                                                                                                                          2 *
                                                                                                                                                                        W'.a₄ *
                                                                                                                                                                      P
                                                                                                                                                                          (0 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) ^
                                                                                                                                                                        3 *
                                                                                                                                                                    P
                                                                                                                                                                      (2 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) *
                                                                                                                                                                  Q
                                                                                                                                                                    (0 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) +
                                                                                                                                                              7 *
                                                                                                                                                                        W'.a₂ *
                                                                                                                                                                      W'.a₄ *
                                                                                                                                                                    P
                                                                                                                                                                        (0 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) ^
                                                                                                                                                                      3 *
                                                                                                                                                                  P
                                                                                                                                                                    (2 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) *
                                                                                                                                                                Q
                                                                                                                                                                  (0 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) -
                                                                                                                                                            3 *
                                                                                                                                                                      W'.a₂ *
                                                                                                                                                                    W'.a₃ *
                                                                                                                                                                  P
                                                                                                                                                                      (0 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) ^
                                                                                                                                                                    3 *
                                                                                                                                                                P
                                                                                                                                                                  (2 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) *
                                                                                                                                                              Q
                                                                                                                                                                (1 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) +
                                                                                                                                                          4 *
                                                                                                                                                                    W'.a₁ ^
                                                                                                                                                                      2 *
                                                                                                                                                                  W'.a₃ ^
                                                                                                                                                                    2 *
                                                                                                                                                                P
                                                                                                                                                                    (0 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) ^
                                                                                                                                                                  3 *
                                                                                                                                                              P
                                                                                                                                                                (2 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) *
                                                                                                                                                            Q
                                                                                                                                                              (2 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) +
                                                                                                                                                        3 *
                                                                                                                                                                  W'.a₁ ^
                                                                                                                                                                    2 *
                                                                                                                                                                W'.a₆ *
                                                                                                                                                              P
                                                                                                                                                                  (0 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) ^
                                                                                                                                                                3 *
                                                                                                                                                            P
                                                                                                                                                              (2 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) *
                                                                                                                                                          Q
                                                                                                                                                            (2 :
                                                                                                                                                              Fin
                                                                                                                                                                3) +
                                                                                                                                                      6 *
                                                                                                                                                                  W'.a₁ *
                                                                                                                                                                W'.a₃ *
                                                                                                                                                              W'.a₄ *
                                                                                                                                                            P
                                                                                                                                                                (0 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) ^
                                                                                                                                                              3 *
                                                                                                                                                          P
                                                                                                                                                            (2 :
                                                                                                                                                              Fin
                                                                                                                                                                3) *
                                                                                                                                                        Q
                                                                                                                                                          (2 :
                                                                                                                                                            Fin
                                                                                                                                                              3) +
                                                                                                                                                    4 *
                                                                                                                                                              W'.a₂ *
                                                                                                                                                            W'.a₃ ^
                                                                                                                                                              2 *
                                                                                                                                                          P
                                                                                                                                                              (0 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) ^
                                                                                                                                                            3 *
                                                                                                                                                        P
                                                                                                                                                          (2 :
                                                                                                                                                            Fin
                                                                                                                                                              3) *
                                                                                                                                                      Q
                                                                                                                                                        (2 :
                                                                                                                                                          Fin
                                                                                                                                                            3) +
                                                                                                                                                  12 *
                                                                                                                                                            W'.a₂ *
                                                                                                                                                          W'.a₆ *
                                                                                                                                                        P
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) ^
                                                                                                                                                          3 *
                                                                                                                                                      P
                                                                                                                                                        (2 :
                                                                                                                                                          Fin
                                                                                                                                                            3) *
                                                                                                                                                    Q
                                                                                                                                                      (2 :
                                                                                                                                                        Fin
                                                                                                                                                          3) +
                                                                                                                                                3 *
                                                                                                                                                        W'.a₄ ^
                                                                                                                                                          2 *
                                                                                                                                                      P
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) ^
                                                                                                                                                        3 *
                                                                                                                                                    P
                                                                                                                                                      (2 :
                                                                                                                                                        Fin
                                                                                                                                                          3) *
                                                                                                                                                  Q
                                                                                                                                                    (2 :
                                                                                                                                                      Fin
                                                                                                                                                        3) -
                                                                                                                                              3 *
                                                                                                                                                      W'.a₁ ^
                                                                                                                                                        2 *
                                                                                                                                                    P
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) ^
                                                                                                                                                      2 *
                                                                                                                                                  P
                                                                                                                                                      (1 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    2 *
                                                                                                                                                Q
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) +
                                                                                                                                            3 *
                                                                                                                                                    W'.a₂ *
                                                                                                                                                  P
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    2 *
                                                                                                                                                P
                                                                                                                                                    (1 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  2 *
                                                                                                                                              Q
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) -
                                                                                                                                          3 *
                                                                                                                                                  W'.a₁ *
                                                                                                                                                P
                                                                                                                                                    (0 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  2 *
                                                                                                                                              P
                                                                                                                                                  (1 :
                                                                                                                                                    Fin
                                                                                                                                                      3) ^
                                                                                                                                                2 *
                                                                                                                                            Q
                                                                                                                                              (1 :
                                                                                                                                                Fin
                                                                                                                                                  3) +
                                                                                                                                        3 *
                                                                                                                                                  W'.a₁ *
                                                                                                                                                W'.a₃ *
                                                                                                                                              P
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) ^
                                                                                                                                                2 *
                                                                                                                                            P
                                                                                                                                                (1 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              2 *
                                                                                                                                          Q
                                                                                                                                            (2 :
                                                                                                                                              Fin
                                                                                                                                                3) +
                                                                                                                                      3 *
                                                                                                                                              W'.a₄ *
                                                                                                                                            P
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              2 *
                                                                                                                                          P
                                                                                                                                              (1 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            2 *
                                                                                                                                        Q
                                                                                                                                          (2 :
                                                                                                                                            Fin
                                                                                                                                              3) -
                                                                                                                                    3 *
                                                                                                                                                W'.a₁ *
                                                                                                                                              W'.a₄ *
                                                                                                                                            P
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              2 *
                                                                                                                                          P
                                                                                                                                            (1 :
                                                                                                                                              Fin
                                                                                                                                                3) *
                                                                                                                                        P
                                                                                                                                          (2 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      Q
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) +
                                                                                                                                  3 *
                                                                                                                                              W'.a₂ *
                                                                                                                                            W'.a₃ *
                                                                                                                                          P
                                                                                                                                              (0 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            2 *
                                                                                                                                        P
                                                                                                                                          (1 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      P
                                                                                                                                        (2 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    Q
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) -
                                                                                                                                3 *
                                                                                                                                          W'.a₄ *
                                                                                                                                        P
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          2 *
                                                                                                                                      P
                                                                                                                                        (1 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    P
                                                                                                                                      (2 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  Q
                                                                                                                                    (1 :
                                                                                                                                      Fin
                                                                                                                                        3) +
                                                                                                                              3 *
                                                                                                                                          W'.a₁ *
                                                                                                                                        W'.a₃ ^
                                                                                                                                          2 *
                                                                                                                                      P
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        2 *
                                                                                                                                    P
                                                                                                                                      (1 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  P
                                                                                                                                    (2 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                Q
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) +
                                                                                                                            3 *
                                                                                                                                        W'.a₃ *
                                                                                                                                      W'.a₄ *
                                                                                                                                    P
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      2 *
                                                                                                                                  P
                                                                                                                                    (1 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                P
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) +
                                                                                                                          3 *
                                                                                                                                    W'.a₂ *
                                                                                                                                  W'.a₃ ^
                                                                                                                                    2 *
                                                                                                                                P
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) ^
                                                                                                                                  2 *
                                                                                                                              P
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 *
                                                                                                                            Q
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) +
                                                                                                                        9 *
                                                                                                                                  W'.a₂ *
                                                                                                                                W'.a₆ *
                                                                                                                              P
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 *
                                                                                                                            P
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 *
                                                                                                                          Q
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) +
                                                                                                                      6 *
                                                                                                                              W'.a₄ ^
                                                                                                                                2 *
                                                                                                                            P
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 *
                                                                                                                          P
                                                                                                                              (2 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 *
                                                                                                                        Q
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) -
                                                                                                                    3 *
                                                                                                                              W'.a₃ *
                                                                                                                            W'.a₄ *
                                                                                                                          P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 *
                                                                                                                        P
                                                                                                                            (2 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 *
                                                                                                                      Q
                                                                                                                        (1 :
                                                                                                                          Fin
                                                                                                                            3) +
                                                                                                                  6 *
                                                                                                                            W'.a₁ *
                                                                                                                          W'.a₃ ^
                                                                                                                            3 *
                                                                                                                        P
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 *
                                                                                                                      P
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 *
                                                                                                                    Q
                                                                                                                      (2 :
                                                                                                                        Fin
                                                                                                                          3) +
                                                                                                                18 *
                                                                                                                            W'.a₁ *
                                                                                                                          W'.a₃ *
                                                                                                                        W'.a₆ *
                                                                                                                      P
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 *
                                                                                                                    P
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 *
                                                                                                                  Q
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) +
                                                                                                              9 *
                                                                                                                        W'.a₃ ^
                                                                                                                          2 *
                                                                                                                      W'.a₄ *
                                                                                                                    P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 *
                                                                                                                  P
                                                                                                                      (2 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    2 *
                                                                                                                Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) +
                                                                                                            27 *
                                                                                                                      W'.a₄ *
                                                                                                                    W'.a₆ *
                                                                                                                  P
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    2 *
                                                                                                                P
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) ^
                                                                                                                  2 *
                                                                                                              Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) -
                                                                                                          3 *
                                                                                                                  W'.a₁ *
                                                                                                                P
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              P
                                                                                                                  (1 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                3 *
                                                                                                            Q
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) -
                                                                                                        3 *
                                                                                                              P
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            P
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              3 *
                                                                                                          Q
                                                                                                            (1 :
                                                                                                              Fin
                                                                                                                3) -
                                                                                                      9 *
                                                                                                                  W'.a₁ *
                                                                                                                W'.a₆ *
                                                                                                              P
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            P
                                                                                                              (1 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          P
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 *
                                                                                                        Q
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) -
                                                                                                    9 *
                                                                                                              W'.a₆ *
                                                                                                            P
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          P
                                                                                                            (1 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        P
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          2 *
                                                                                                      Q
                                                                                                        (1 :
                                                                                                          Fin
                                                                                                            3) +
                                                                                                  W'.a₁ ^
                                                                                                              2 *
                                                                                                            W'.a₂ *
                                                                                                          W'.a₆ *
                                                                                                        P
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      P
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        3 *
                                                                                                    Q
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) -
                                                                                                W'.a₁ *
                                                                                                            W'.a₂ *
                                                                                                          W'.a₃ *
                                                                                                        W'.a₄ *
                                                                                                      P
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    P
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      3 *
                                                                                                  Q
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) -
                                                                                              3 *
                                                                                                          W'.a₁ *
                                                                                                        W'.a₃ *
                                                                                                      W'.a₆ *
                                                                                                    P
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  P
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    3 *
                                                                                                Q
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) +
                                                                                            W'.a₂ ^
                                                                                                      2 *
                                                                                                    W'.a₃ ^
                                                                                                      2 *
                                                                                                  P
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                P
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  3 *
                                                                                              Q
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) +
                                                                                          4 *
                                                                                                    W'.a₂ ^
                                                                                                      2 *
                                                                                                  W'.a₆ *
                                                                                                P
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              P
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                3 *
                                                                                            Q
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) -
                                                                                        W'.a₂ *
                                                                                                W'.a₄ ^
                                                                                                  2 *
                                                                                              P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            P
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              3 *
                                                                                          Q
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) +
                                                                                      3 *
                                                                                                W'.a₃ ^
                                                                                                  2 *
                                                                                              W'.a₄ *
                                                                                            P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          P
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            3 *
                                                                                        Q
                                                                                          (0 :
                                                                                            Fin 3) +
                                                                                    12 * W'.a₄ *
                                                                                            W'.a₆ *
                                                                                          P
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) *
                                                                                        P
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          3 *
                                                                                      Q
                                                                                        (0 :
                                                                                          Fin 3) -
                                                                                  3 * W'.a₃ *
                                                                                          W'.a₆ *
                                                                                        P
                                                                                          (0 :
                                                                                            Fin 3) *
                                                                                      P
                                                                                          (2 :
                                                                                            Fin 3) ^
                                                                                        3 *
                                                                                    Q (1 : Fin 3) +
                                                                                W'.a₁ ^ 3 * W'.a₃ *
                                                                                        W'.a₆ *
                                                                                      P
                                                                                        (0 :
                                                                                          Fin 3) *
                                                                                    P (2 : Fin 3) ^
                                                                                      3 *
                                                                                  Q (2 : Fin 3) -
                                                                              W'.a₁ ^ 2 *
                                                                                        W'.a₃ ^ 2 *
                                                                                      W'.a₄ *
                                                                                    P (0 : Fin 3) *
                                                                                  P (2 : Fin 3) ^
                                                                                    3 *
                                                                                Q (2 : Fin 3) +
                                                                            W'.a₁ ^ 2 * W'.a₄ *
                                                                                    W'.a₆ *
                                                                                  P (0 : Fin 3) *
                                                                                P (2 : Fin 3) ^ 3 *
                                                                              Q (2 : Fin 3) +
                                                                          W'.a₁ * W'.a₂ *
                                                                                  W'.a₃ ^ 3 *
                                                                                P (0 : Fin 3) *
                                                                              P (2 : Fin 3) ^ 3 *
                                                                            Q (2 : Fin 3) +
                                                                        4 * W'.a₁ * W'.a₂ * W'.a₃ *
                                                                                W'.a₆ *
                                                                              P (0 : Fin 3) *
                                                                            P (2 : Fin 3) ^ 3 *
                                                                          Q (2 : Fin 3) -
                                                                      2 * W'.a₁ * W'.a₃ *
                                                                              W'.a₄ ^ 2 *
                                                                            P (0 : Fin 3) *
                                                                          P (2 : Fin 3) ^ 3 *
                                                                        Q (2 : Fin 3) +
                                                                    W'.a₂ * W'.a₃ ^ 2 * W'.a₄ *
                                                                          P (0 : Fin 3) *
                                                                        P (2 : Fin 3) ^ 3 *
                                                                      Q (2 : Fin 3) +
                                                                  4 * W'.a₂ * W'.a₄ * W'.a₆ *
                                                                        P (0 : Fin 3) *
                                                                      P (2 : Fin 3) ^ 3 *
                                                                    Q (2 : Fin 3) +
                                                                3 * W'.a₃ ^ 4 * P (0 : Fin 3) *
                                                                    P (2 : Fin 3) ^ 3 *
                                                                  Q (2 : Fin 3) +
                                                              21 * W'.a₃ ^ 2 * W'.a₆ *
                                                                    P (0 : Fin 3) *
                                                                  P (2 : Fin 3) ^ 3 *
                                                                Q (2 : Fin 3) -
                                                            W'.a₄ ^ 3 * P (0 : Fin 3) *
                                                                P (2 : Fin 3) ^ 3 *
                                                              Q (2 : Fin 3) +
                                                          36 * W'.a₆ ^ 2 * P (0 : Fin 3) *
                                                              P (2 : Fin 3) ^ 3 *
                                                            Q (2 : Fin 3) -
                                                        W'.a₁ ^ 3 * W'.a₆ * P (1 : Fin 3) *
                                                            P (2 : Fin 3) ^ 3 *
                                                          Q (0 : Fin 3) +
                                                      W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P (1 : Fin 3) *
                                                          P (2 : Fin 3) ^ 3 *
                                                        Q (0 : Fin 3) -
                                                    W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) *
                                                        P (2 : Fin 3) ^ 3 *
                                                      Q (0 : Fin 3) -
                                                  4 * W'.a₁ * W'.a₂ * W'.a₆ * P (1 : Fin 3) *
                                                      P (2 : Fin 3) ^ 3 *
                                                    Q (0 : Fin 3) +
                                                W'.a₁ * W'.a₄ ^ 2 * P (1 : Fin 3) *
                                                    P (2 : Fin 3) ^ 3 *
                                                  Q (0 : Fin 3) -
                                              W'.a₁ ^ 2 * W'.a₆ * P (1 : Fin 3) *
                                                  P (2 : Fin 3) ^ 3 *
                                                Q (1 : Fin 3) +
                                            W'.a₁ * W'.a₃ * W'.a₄ * P (1 : Fin 3) *
                                                P (2 : Fin 3) ^ 3 *
                                              Q (1 : Fin 3) -
                                          W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                            Q (1 : Fin 3) -
                                        4 * W'.a₂ * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                          Q (1 : Fin 3) +
                                      W'.a₄ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                        Q (1 : Fin 3) +
                                    W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) -
                                  W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) +
                                W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) +
                              4 * W'.a₂ * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) -
                            W'.a₄ ^ 3 * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) +
                          W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                        3 * W'.a₁ ^ 2 * W'.a₆ ^ 2 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
                      W'.a₁ * W'.a₃ ^ 3 * W'.a₄ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
                    3 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                  W'.a₂ * W'.a₃ ^ 4 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                7 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
              12 * W'.a₂ * W'.a₆ ^ 2 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
            W'.a₃ ^ 2 * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
          3 * W'.a₄ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3)) *
        (equation_iff Q).mp hQ


-- @@ L377-436 expanded
/-- **(T-W7.0c(c3))** The `XZ` minor of the two addition laws vanishes on the curve:
law 1 and law 2 are projectively proportional wherever both are defined. CAS-certified
cofactors (Y-first reduction; see `scripts/tw7-p1-bosma-lenstra/cof_MXZ_P.txt`, `_Q.txt`). -/
lemma addX_mul_dblAddZ {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * W'.dblAddZ P Q = W'.addZ P Q * W'.dblAddX P Q := by
  linear_combination (norm := (law_simp; ring1))
    (3 * P (0 : Fin 3) * Q (0 : Fin 3) ^ 3 * Q (1 : Fin 3) +
                                                                                                                                    W'.a₁ ^
                                                                                                                                            3 *
                                                                                                                                          P
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) *
                                                                                                                                        Q
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          3 *
                                                                                                                                      Q
                                                                                                                                        (2 :
                                                                                                                                          Fin
                                                                                                                                            3) +
                                                                                                                                  W'.a₁ *
                                                                                                                                          W'.a₂ *
                                                                                                                                        P
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      Q
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        3 *
                                                                                                                                    Q
                                                                                                                                      (2 :
                                                                                                                                        Fin
                                                                                                                                          3) +
                                                                                                                                6 *
                                                                                                                                        W'.a₃ *
                                                                                                                                      P
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    Q
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      3 *
                                                                                                                                  Q
                                                                                                                                    (2 :
                                                                                                                                      Fin
                                                                                                                                        3) +
                                                                                                                              3 *
                                                                                                                                        W'.a₁ ^
                                                                                                                                          2 *
                                                                                                                                      P
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    Q
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      2 *
                                                                                                                                  Q
                                                                                                                                    (1 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                Q
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) +
                                                                                                                            3 *
                                                                                                                                      W'.a₂ *
                                                                                                                                    P
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  Q
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) ^
                                                                                                                                    2 *
                                                                                                                                Q
                                                                                                                                  (1 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) +
                                                                                                                          3 *
                                                                                                                                    W'.a₁ ^
                                                                                                                                      2 *
                                                                                                                                  W'.a₃ *
                                                                                                                                P
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 *
                                                                                                                            Q
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 +
                                                                                                                        3 *
                                                                                                                                  W'.a₁ *
                                                                                                                                W'.a₄ *
                                                                                                                              P
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) *
                                                                                                                            Q
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 *
                                                                                                                          Q
                                                                                                                              (2 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 +
                                                                                                                      6 *
                                                                                                                                W'.a₂ *
                                                                                                                              W'.a₃ *
                                                                                                                            P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) *
                                                                                                                          Q
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 *
                                                                                                                        Q
                                                                                                                            (2 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 -
                                                                                                                    3 *
                                                                                                                                W'.a₁ *
                                                                                                                              W'.a₃ *
                                                                                                                            P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) *
                                                                                                                          Q
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        Q
                                                                                                                          (1 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      Q
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 +
                                                                                                                  3 *
                                                                                                                            W'.a₄ *
                                                                                                                          P
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        Q
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      Q
                                                                                                                        (1 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 +
                                                                                                                3 *
                                                                                                                          W'.a₁ *
                                                                                                                        W'.a₃ ^
                                                                                                                          2 *
                                                                                                                      P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                      (2 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    3 +
                                                                                                              9 *
                                                                                                                        W'.a₁ *
                                                                                                                      W'.a₆ *
                                                                                                                    P
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) ^
                                                                                                                  3 +
                                                                                                            6 *
                                                                                                                      W'.a₃ *
                                                                                                                    W'.a₄ *
                                                                                                                  P
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                3 -
                                                                                                          3 *
                                                                                                                P
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                  (1 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                3 *
                                                                                                            Q
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) -
                                                                                                        9 *
                                                                                                                W'.a₃ *
                                                                                                              P
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              2 *
                                                                                                          Q
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 -
                                                                                                      6 *
                                                                                                              W'.a₃ ^
                                                                                                                2 *
                                                                                                            P
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                            (1 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        Q
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          3 +
                                                                                                    3 *
                                                                                                            W'.a₆ *
                                                                                                          P
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        Q
                                                                                                          (1 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        3 +
                                                                                                  W'.a₁ ^
                                                                                                          3 *
                                                                                                        W'.a₆ *
                                                                                                      P
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      4 -
                                                                                                W'.a₁ ^
                                                                                                          2 *
                                                                                                        W'.a₃ *
                                                                                                      W'.a₄ *
                                                                                                    P
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    4 +
                                                                                              W'.a₁ *
                                                                                                      W'.a₂ *
                                                                                                    W'.a₃ ^
                                                                                                      2 *
                                                                                                  P
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  4 +
                                                                                            4 *
                                                                                                      W'.a₁ *
                                                                                                    W'.a₂ *
                                                                                                  W'.a₆ *
                                                                                                P
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              Q
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                4 -
                                                                                          W'.a₁ *
                                                                                                W'.a₄ ^
                                                                                                  2 *
                                                                                              P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              4 +
                                                                                        6 * W'.a₃ *
                                                                                              W'.a₆ *
                                                                                            P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            4 +
                                                                                      W'.a₁ ^ 2 *
                                                                                            P
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            3 *
                                                                                        Q
                                                                                          (2 :
                                                                                            Fin 3) +
                                                                                    W'.a₂ *
                                                                                          P
                                                                                            (1 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          3 *
                                                                                      Q
                                                                                        (2 :
                                                                                          Fin 3) +
                                                                                  3 * W'.a₁ *
                                                                                          P
                                                                                            (1 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          2 *
                                                                                      Q
                                                                                        (1 :
                                                                                          Fin 3) *
                                                                                    Q (2 : Fin 3) +
                                                                                3 * W'.a₁ * W'.a₃ *
                                                                                      P
                                                                                        (1 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) ^
                                                                                      2 *
                                                                                  Q (2 : Fin 3) ^
                                                                                    2 +
                                                                              3 * W'.a₄ *
                                                                                    P (1 : Fin 3) *
                                                                                  Q (0 : Fin 3) ^
                                                                                    2 *
                                                                                Q (2 : Fin 3) ^ 2 +
                                                                            3 * P (1 : Fin 3) *
                                                                                  Q (0 : Fin 3) *
                                                                                Q (1 : Fin 3) ^ 2 *
                                                                              Q (2 : Fin 3) +
                                                                          3 * W'.a₃ *
                                                                                  P (1 : Fin 3) *
                                                                                Q (0 : Fin 3) *
                                                                              Q (1 : Fin 3) *
                                                                            Q (2 : Fin 3) ^ 2 +
                                                                        3 * W'.a₃ ^ 2 *
                                                                              P (1 : Fin 3) *
                                                                            Q (0 : Fin 3) *
                                                                          Q (2 : Fin 3) ^ 3 +
                                                                      9 * W'.a₆ * P (1 : Fin 3) *
                                                                          Q (0 : Fin 3) *
                                                                        Q (2 : Fin 3) ^ 3 +
                                                                    W'.a₁ ^ 2 * W'.a₆ *
                                                                        P (1 : Fin 3) *
                                                                      Q (2 : Fin 3) ^ 4 -
                                                                  W'.a₁ * W'.a₃ * W'.a₄ *
                                                                      P (1 : Fin 3) *
                                                                    Q (2 : Fin 3) ^ 4 +
                                                                W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) *
                                                                  Q (2 : Fin 3) ^ 4 +
                                                              4 * W'.a₂ * W'.a₆ * P (1 : Fin 3) *
                                                                Q (2 : Fin 3) ^ 4 -
                                                            W'.a₄ ^ 2 * P (1 : Fin 3) *
                                                              Q (2 : Fin 3) ^ 4 +
                                                          W'.a₁ ^ 2 * P (2 : Fin 3) *
                                                              Q (0 : Fin 3) ^ 3 *
                                                            Q (1 : Fin 3) +
                                                        W'.a₂ * P (2 : Fin 3) * Q (0 : Fin 3) ^ 3 *
                                                          Q (1 : Fin 3) +
                                                      W'.a₁ ^ 2 * W'.a₃ * P (2 : Fin 3) *
                                                          Q (0 : Fin 3) ^ 3 *
                                                        Q (2 : Fin 3) +
                                                    W'.a₂ * W'.a₃ * P (2 : Fin 3) *
                                                        Q (0 : Fin 3) ^ 3 *
                                                      Q (2 : Fin 3) +
                                                  3 * W'.a₁ * P (2 : Fin 3) * Q (0 : Fin 3) ^ 2 *
                                                    Q (1 : Fin 3) ^ 2 +
                                                6 * W'.a₁ * W'.a₃ * P (2 : Fin 3) *
                                                      Q (0 : Fin 3) ^ 2 *
                                                    Q (1 : Fin 3) *
                                                  Q (2 : Fin 3) +
                                              3 * W'.a₄ * P (2 : Fin 3) * Q (0 : Fin 3) ^ 2 *
                                                  Q (1 : Fin 3) *
                                                Q (2 : Fin 3) +
                                            3 * W'.a₁ * W'.a₃ ^ 2 * P (2 : Fin 3) *
                                                Q (0 : Fin 3) ^ 2 *
                                              Q (2 : Fin 3) ^ 2 +
                                          3 * W'.a₃ * W'.a₄ * P (2 : Fin 3) * Q (0 : Fin 3) ^ 2 *
                                            Q (2 : Fin 3) ^ 2 +
                                        3 * P (2 : Fin 3) * Q (0 : Fin 3) * Q (1 : Fin 3) ^ 3 +
                                      6 * W'.a₃ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                          Q (1 : Fin 3) ^ 2 *
                                        Q (2 : Fin 3) +
                                    6 * W'.a₃ ^ 2 * P (2 : Fin 3) * Q (0 : Fin 3) * Q (1 : Fin 3) *
                                      Q (2 : Fin 3) ^ 2 +
                                  9 * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) * Q (1 : Fin 3) *
                                    Q (2 : Fin 3) ^ 2 +
                                3 * W'.a₃ ^ 3 * P (2 : Fin 3) * Q (0 : Fin 3) * Q (2 : Fin 3) ^ 3 +
                              9 * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                Q (2 : Fin 3) ^ 3 +
                            W'.a₁ ^ 2 * W'.a₆ * P (2 : Fin 3) * Q (1 : Fin 3) * Q (2 : Fin 3) ^ 3 -
                          W'.a₁ * W'.a₃ * W'.a₄ * P (2 : Fin 3) * Q (1 : Fin 3) *
                            Q (2 : Fin 3) ^ 3 +
                        W'.a₂ * W'.a₃ ^ 2 * P (2 : Fin 3) * Q (1 : Fin 3) * Q (2 : Fin 3) ^ 3 +
                      4 * W'.a₂ * W'.a₆ * P (2 : Fin 3) * Q (1 : Fin 3) * Q (2 : Fin 3) ^ 3 -
                    W'.a₄ ^ 2 * P (2 : Fin 3) * Q (1 : Fin 3) * Q (2 : Fin 3) ^ 3 +
                  W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
              W'.a₂ * W'.a₃ ^ 3 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
            4 * W'.a₂ * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
          W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4) *
        (equation_iff P).mp hP +
      (-3 * P (0 : Fin 3) ^ 4 * Q (1 : Fin 3) - W'.a₁ ^ 3 * P (0 : Fin 3) ^ 4 * Q (2 : Fin 3) -
                                                                                              W'.a₁ *
                                                                                                    W'.a₂ *
                                                                                                  P
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    4 *
                                                                                                Q
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) -
                                                                                            6 *
                                                                                                  W'.a₃ *
                                                                                                P
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  4 *
                                                                                              Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) -
                                                                                          4 *
                                                                                                  W'.a₁ ^
                                                                                                    2 *
                                                                                                P
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  3 *
                                                                                              P
                                                                                                (1 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) -
                                                                                        W'.a₂ *
                                                                                              P
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                3 *
                                                                                            P
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) -
                                                                                      W'.a₁ ^ 2 *
                                                                                            P
                                                                                                (0 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              3 *
                                                                                          P
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                          (1 :
                                                                                            Fin 3) -
                                                                                    4 * W'.a₂ *
                                                                                          P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            3 *
                                                                                        P
                                                                                          (2 :
                                                                                            Fin 3) *
                                                                                      Q
                                                                                        (1 :
                                                                                          Fin 3) -
                                                                                  4 * W'.a₁ ^ 2 *
                                                                                          W'.a₃ *
                                                                                        P
                                                                                            (0 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          3 *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (2 : Fin 3) -
                                                                                3 * W'.a₁ * W'.a₄ *
                                                                                      P
                                                                                          (0 :
                                                                                            Fin 3) ^
                                                                                        3 *
                                                                                    P (2 : Fin 3) *
                                                                                  Q (2 : Fin 3) -
                                                                              7 * W'.a₂ * W'.a₃ *
                                                                                    P (0 : Fin 3) ^
                                                                                      3 *
                                                                                  P (2 : Fin 3) *
                                                                                Q (2 : Fin 3) -
                                                                            6 * W'.a₁ *
                                                                                  P (0 : Fin 3) ^
                                                                                    2 *
                                                                                P (1 : Fin 3) ^ 2 *
                                                                              Q (2 : Fin 3) -
                                                                          3 * W'.a₁ * W'.a₃ *
                                                                                  P (0 : Fin 3) ^
                                                                                    2 *
                                                                                P (1 : Fin 3) *
                                                                              P (2 : Fin 3) *
                                                                            Q (2 : Fin 3) -
                                                                        3 * W'.a₄ *
                                                                                P (0 : Fin 3) ^ 2 *
                                                                              P (1 : Fin 3) *
                                                                            P (2 : Fin 3) *
                                                                          Q (2 : Fin 3) -
                                                                      3 * W'.a₁ * W'.a₃ *
                                                                            P (0 : Fin 3) ^ 2 *
                                                                          P (2 : Fin 3) ^ 2 *
                                                                        Q (1 : Fin 3) -
                                                                    6 * W'.a₄ * P (0 : Fin 3) ^ 2 *
                                                                        P (2 : Fin 3) ^ 2 *
                                                                      Q (1 : Fin 3) -
                                                                  6 * W'.a₁ * W'.a₃ ^ 2 *
                                                                        P (0 : Fin 3) ^ 2 *
                                                                      P (2 : Fin 3) ^ 2 *
                                                                    Q (2 : Fin 3) -
                                                                9 * W'.a₁ * W'.a₆ *
                                                                      P (0 : Fin 3) ^ 2 *
                                                                    P (2 : Fin 3) ^ 2 *
                                                                  Q (2 : Fin 3) -
                                                              9 * W'.a₃ * W'.a₄ *
                                                                    P (0 : Fin 3) ^ 2 *
                                                                  P (2 : Fin 3) ^ 2 *
                                                                Q (2 : Fin 3) -
                                                            3 * P (0 : Fin 3) * P (1 : Fin 3) ^ 3 *
                                                              Q (2 : Fin 3) -
                                                          9 * W'.a₆ * P (0 : Fin 3) *
                                                                P (1 : Fin 3) *
                                                              P (2 : Fin 3) ^ 2 *
                                                            Q (2 : Fin 3) -
                                                        3 * W'.a₃ ^ 2 * P (0 : Fin 3) *
                                                            P (2 : Fin 3) ^ 3 *
                                                          Q (1 : Fin 3) -
                                                      12 * W'.a₆ * P (0 : Fin 3) *
                                                          P (2 : Fin 3) ^ 3 *
                                                        Q (1 : Fin 3) -
                                                    W'.a₁ ^ 3 * W'.a₆ * P (0 : Fin 3) *
                                                        P (2 : Fin 3) ^ 3 *
                                                      Q (2 : Fin 3) +
                                                  W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P (0 : Fin 3) *
                                                      P (2 : Fin 3) ^ 3 *
                                                    Q (2 : Fin 3) -
                                                W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P (0 : Fin 3) *
                                                    P (2 : Fin 3) ^ 3 *
                                                  Q (2 : Fin 3) -
                                              4 * W'.a₁ * W'.a₂ * W'.a₆ * P (0 : Fin 3) *
                                                  P (2 : Fin 3) ^ 3 *
                                                Q (2 : Fin 3) +
                                            W'.a₁ * W'.a₄ ^ 2 * P (0 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                              Q (2 : Fin 3) -
                                          3 * W'.a₃ ^ 3 * P (0 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                            Q (2 : Fin 3) -
                                        15 * W'.a₃ * W'.a₆ * P (0 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                          Q (2 : Fin 3) -
                                      W'.a₁ ^ 2 * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                        Q (2 : Fin 3) +
                                    W'.a₁ * W'.a₃ * W'.a₄ * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                      Q (2 : Fin 3) -
                                  W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                    Q (2 : Fin 3) -
                                4 * W'.a₂ * W'.a₆ * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                  Q (2 : Fin 3) +
                              W'.a₄ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 * Q (2 : Fin 3) -
                            W'.a₁ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (1 : Fin 3) +
                          W'.a₁ * W'.a₃ * W'.a₄ * P (2 : Fin 3) ^ 4 * Q (1 : Fin 3) -
                        W'.a₂ * W'.a₃ ^ 2 * P (2 : Fin 3) ^ 4 * Q (1 : Fin 3) -
                      4 * W'.a₂ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (1 : Fin 3) +
                    W'.a₄ ^ 2 * P (2 : Fin 3) ^ 4 * Q (1 : Fin 3) -
                  W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
              W'.a₂ * W'.a₃ ^ 3 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
            4 * W'.a₂ * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
          W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3)) *
        (equation_iff Q).mp hQ


-- @@ L438-530 expanded
/-- **(T-W7.0c(c3))** The `YZ` minor of the two addition laws vanishes on the curve:
law 1 and law 2 are projectively proportional wherever both are defined. CAS-certified
cofactors (Y-first reduction; see `scripts/tw7-p1-bosma-lenstra/cof_MYZ_P.txt`, `_Q.txt`). -/
lemma addY_mul_dblAddZ {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addY P Q * W'.dblAddZ P Q = W'.addZ P Q * W'.dblAddY P Q := by
  linear_combination (norm := (law_simp; ring1))
    (-3 * W'.a₁ ^ 2 * P (0 : Fin 3) * Q (0 : Fin 3) ^ 4 -
                                                                                                                                                                                              6 *
                                                                                                                                                                                                    W'.a₂ *
                                                                                                                                                                                                  P
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) *
                                                                                                                                                                                                Q
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                  4 -
                                                                                                                                                                                            9 *
                                                                                                                                                                                                    W'.a₁ *
                                                                                                                                                                                                  P
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) *
                                                                                                                                                                                                Q
                                                                                                                                                                                                    (0 :
                                                                                                                                                                                                      Fin
                                                                                                                                                                                                        3) ^
                                                                                                                                                                                                  3 *
                                                                                                                                                                                              Q
                                                                                                                                                                                                (1 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) -
                                                                                                                                                                                          W'.a₁ ^
                                                                                                                                                                                                  4 *
                                                                                                                                                                                                P
                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) *
                                                                                                                                                                                              Q
                                                                                                                                                                                                  (0 :
                                                                                                                                                                                                    Fin
                                                                                                                                                                                                      3) ^
                                                                                                                                                                                                3 *
                                                                                                                                                                                            Q
                                                                                                                                                                                              (2 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) -
                                                                                                                                                                                        2 *
                                                                                                                                                                                                  W'.a₁ ^
                                                                                                                                                                                                    2 *
                                                                                                                                                                                                W'.a₂ *
                                                                                                                                                                                              P
                                                                                                                                                                                                (0 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) *
                                                                                                                                                                                            Q
                                                                                                                                                                                                (0 :
                                                                                                                                                                                                  Fin
                                                                                                                                                                                                    3) ^
                                                                                                                                                                                              3 *
                                                                                                                                                                                          Q
                                                                                                                                                                                            (2 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) -
                                                                                                                                                                                      15 *
                                                                                                                                                                                                W'.a₁ *
                                                                                                                                                                                              W'.a₃ *
                                                                                                                                                                                            P
                                                                                                                                                                                              (0 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) *
                                                                                                                                                                                          Q
                                                                                                                                                                                              (0 :
                                                                                                                                                                                                Fin
                                                                                                                                                                                                  3) ^
                                                                                                                                                                                            3 *
                                                                                                                                                                                        Q
                                                                                                                                                                                          (2 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) -
                                                                                                                                                                                    4 *
                                                                                                                                                                                            W'.a₂ ^
                                                                                                                                                                                              2 *
                                                                                                                                                                                          P
                                                                                                                                                                                            (0 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) *
                                                                                                                                                                                        Q
                                                                                                                                                                                            (0 :
                                                                                                                                                                                              Fin
                                                                                                                                                                                                3) ^
                                                                                                                                                                                          3 *
                                                                                                                                                                                      Q
                                                                                                                                                                                        (2 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) -
                                                                                                                                                                                  12 *
                                                                                                                                                                                          W'.a₄ *
                                                                                                                                                                                        P
                                                                                                                                                                                          (0 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) *
                                                                                                                                                                                      Q
                                                                                                                                                                                          (0 :
                                                                                                                                                                                            Fin
                                                                                                                                                                                              3) ^
                                                                                                                                                                                        3 *
                                                                                                                                                                                    Q
                                                                                                                                                                                      (2 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) -
                                                                                                                                                                                9 *
                                                                                                                                                                                      P
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) *
                                                                                                                                                                                    Q
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) ^
                                                                                                                                                                                      2 *
                                                                                                                                                                                  Q
                                                                                                                                                                                      (1 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) ^
                                                                                                                                                                                    2 -
                                                                                                                                                                              3 *
                                                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                                          3 *
                                                                                                                                                                                      P
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) *
                                                                                                                                                                                    Q
                                                                                                                                                                                        (0 :
                                                                                                                                                                                          Fin
                                                                                                                                                                                            3) ^
                                                                                                                                                                                      2 *
                                                                                                                                                                                  Q
                                                                                                                                                                                    (1 :
                                                                                                                                                                                      Fin
                                                                                                                                                                                        3) *
                                                                                                                                                                                Q
                                                                                                                                                                                  (2 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) -
                                                                                                                                                                            9 *
                                                                                                                                                                                      W'.a₃ *
                                                                                                                                                                                    P
                                                                                                                                                                                      (0 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) *
                                                                                                                                                                                  Q
                                                                                                                                                                                      (0 :
                                                                                                                                                                                        Fin
                                                                                                                                                                                          3) ^
                                                                                                                                                                                    2 *
                                                                                                                                                                                Q
                                                                                                                                                                                  (1 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) *
                                                                                                                                                                              Q
                                                                                                                                                                                (2 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) -
                                                                                                                                                                          3 *
                                                                                                                                                                                    W'.a₁ ^
                                                                                                                                                                                      3 *
                                                                                                                                                                                  W'.a₃ *
                                                                                                                                                                                P
                                                                                                                                                                                  (0 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) *
                                                                                                                                                                              Q
                                                                                                                                                                                  (0 :
                                                                                                                                                                                    Fin
                                                                                                                                                                                      3) ^
                                                                                                                                                                                2 *
                                                                                                                                                                            Q
                                                                                                                                                                                (2 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) ^
                                                                                                                                                                              2 -
                                                                                                                                                                        3 *
                                                                                                                                                                                  W'.a₁ ^
                                                                                                                                                                                    2 *
                                                                                                                                                                                W'.a₄ *
                                                                                                                                                                              P
                                                                                                                                                                                (0 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) *
                                                                                                                                                                            Q
                                                                                                                                                                                (0 :
                                                                                                                                                                                  Fin
                                                                                                                                                                                    3) ^
                                                                                                                                                                              2 *
                                                                                                                                                                          Q
                                                                                                                                                                              (2 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) ^
                                                                                                                                                                            2 -
                                                                                                                                                                      9 *
                                                                                                                                                                                  W'.a₁ *
                                                                                                                                                                                W'.a₂ *
                                                                                                                                                                              W'.a₃ *
                                                                                                                                                                            P
                                                                                                                                                                              (0 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) *
                                                                                                                                                                          Q
                                                                                                                                                                              (0 :
                                                                                                                                                                                Fin
                                                                                                                                                                                  3) ^
                                                                                                                                                                            2 *
                                                                                                                                                                        Q
                                                                                                                                                                            (2 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) ^
                                                                                                                                                                          2 -
                                                                                                                                                                    9 *
                                                                                                                                                                              W'.a₂ *
                                                                                                                                                                            W'.a₄ *
                                                                                                                                                                          P
                                                                                                                                                                            (0 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) *
                                                                                                                                                                        Q
                                                                                                                                                                            (0 :
                                                                                                                                                                              Fin
                                                                                                                                                                                3) ^
                                                                                                                                                                          2 *
                                                                                                                                                                      Q
                                                                                                                                                                          (2 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) ^
                                                                                                                                                                        2 -
                                                                                                                                                                  9 *
                                                                                                                                                                          W'.a₃ ^
                                                                                                                                                                            2 *
                                                                                                                                                                        P
                                                                                                                                                                          (0 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) *
                                                                                                                                                                      Q
                                                                                                                                                                          (0 :
                                                                                                                                                                            Fin
                                                                                                                                                                              3) ^
                                                                                                                                                                        2 *
                                                                                                                                                                    Q
                                                                                                                                                                        (2 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) ^
                                                                                                                                                                      2 -
                                                                                                                                                                27 *
                                                                                                                                                                        W'.a₆ *
                                                                                                                                                                      P
                                                                                                                                                                        (0 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) *
                                                                                                                                                                    Q
                                                                                                                                                                        (0 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) ^
                                                                                                                                                                      2 *
                                                                                                                                                                  Q
                                                                                                                                                                      (2 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) ^
                                                                                                                                                                    2 -
                                                                                                                                                              3 *
                                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                          2 *
                                                                                                                                                                      P
                                                                                                                                                                        (0 :
                                                                                                                                                                          Fin
                                                                                                                                                                            3) *
                                                                                                                                                                    Q
                                                                                                                                                                      (0 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) *
                                                                                                                                                                  Q
                                                                                                                                                                      (1 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) ^
                                                                                                                                                                    2 *
                                                                                                                                                                Q
                                                                                                                                                                  (2 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) +
                                                                                                                                                            3 *
                                                                                                                                                                        W'.a₁ ^
                                                                                                                                                                          2 *
                                                                                                                                                                      W'.a₃ *
                                                                                                                                                                    P
                                                                                                                                                                      (0 :
                                                                                                                                                                        Fin
                                                                                                                                                                          3) *
                                                                                                                                                                  Q
                                                                                                                                                                    (0 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) *
                                                                                                                                                                Q
                                                                                                                                                                  (1 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) *
                                                                                                                                                              Q
                                                                                                                                                                  (2 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) ^
                                                                                                                                                                2 +
                                                                                                                                                          3 *
                                                                                                                                                                      W'.a₁ *
                                                                                                                                                                    W'.a₄ *
                                                                                                                                                                  P
                                                                                                                                                                    (0 :
                                                                                                                                                                      Fin
                                                                                                                                                                        3) *
                                                                                                                                                                Q
                                                                                                                                                                  (0 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) *
                                                                                                                                                              Q
                                                                                                                                                                (1 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) *
                                                                                                                                                            Q
                                                                                                                                                                (2 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) ^
                                                                                                                                                              2 -
                                                                                                                                                        3 *
                                                                                                                                                                  W'.a₁ ^
                                                                                                                                                                    2 *
                                                                                                                                                                W'.a₃ ^
                                                                                                                                                                  2 *
                                                                                                                                                              P
                                                                                                                                                                (0 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) *
                                                                                                                                                            Q
                                                                                                                                                              (0 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) *
                                                                                                                                                          Q
                                                                                                                                                              (2 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) ^
                                                                                                                                                            3 -
                                                                                                                                                      12 *
                                                                                                                                                                W'.a₁ ^
                                                                                                                                                                  2 *
                                                                                                                                                              W'.a₆ *
                                                                                                                                                            P
                                                                                                                                                              (0 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) *
                                                                                                                                                          Q
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) *
                                                                                                                                                        Q
                                                                                                                                                            (2 :
                                                                                                                                                              Fin
                                                                                                                                                                3) ^
                                                                                                                                                          3 -
                                                                                                                                                    3 *
                                                                                                                                                                W'.a₁ *
                                                                                                                                                              W'.a₃ *
                                                                                                                                                            W'.a₄ *
                                                                                                                                                          P
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) *
                                                                                                                                                        Q
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) *
                                                                                                                                                      Q
                                                                                                                                                          (2 :
                                                                                                                                                            Fin
                                                                                                                                                              3) ^
                                                                                                                                                        3 -
                                                                                                                                                  6 *
                                                                                                                                                            W'.a₂ *
                                                                                                                                                          W'.a₃ ^
                                                                                                                                                            2 *
                                                                                                                                                        P
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) *
                                                                                                                                                      Q
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) *
                                                                                                                                                    Q
                                                                                                                                                        (2 :
                                                                                                                                                          Fin
                                                                                                                                                            3) ^
                                                                                                                                                      3 -
                                                                                                                                                24 *
                                                                                                                                                          W'.a₂ *
                                                                                                                                                        W'.a₆ *
                                                                                                                                                      P
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) *
                                                                                                                                                    Q
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) *
                                                                                                                                                  Q
                                                                                                                                                      (2 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    3 +
                                                                                                                                              6 *
                                                                                                                                                        W'.a₁ *
                                                                                                                                                      W'.a₃ *
                                                                                                                                                    P
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) *
                                                                                                                                                  Q
                                                                                                                                                      (1 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    2 *
                                                                                                                                                Q
                                                                                                                                                    (2 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  2 +
                                                                                                                                            3 *
                                                                                                                                                    W'.a₄ *
                                                                                                                                                  P
                                                                                                                                                    (0 :
                                                                                                                                                      Fin
                                                                                                                                                        3) *
                                                                                                                                                Q
                                                                                                                                                    (1 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  2 *
                                                                                                                                              Q
                                                                                                                                                  (2 :
                                                                                                                                                    Fin
                                                                                                                                                      3) ^
                                                                                                                                                2 +
                                                                                                                                          6 *
                                                                                                                                                    W'.a₁ *
                                                                                                                                                  W'.a₃ ^
                                                                                                                                                    2 *
                                                                                                                                                P
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) *
                                                                                                                                              Q
                                                                                                                                                (1 :
                                                                                                                                                  Fin
                                                                                                                                                    3) *
                                                                                                                                            Q
                                                                                                                                                (2 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              3 +
                                                                                                                                        3 *
                                                                                                                                                  W'.a₃ *
                                                                                                                                                W'.a₄ *
                                                                                                                                              P
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) *
                                                                                                                                            Q
                                                                                                                                              (1 :
                                                                                                                                                Fin
                                                                                                                                                  3) *
                                                                                                                                          Q
                                                                                                                                              (2 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            3 -
                                                                                                                                      W'.a₁ ^
                                                                                                                                              4 *
                                                                                                                                            W'.a₆ *
                                                                                                                                          P
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) *
                                                                                                                                        Q
                                                                                                                                            (2 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          4 +
                                                                                                                                    W'.a₁ ^
                                                                                                                                              3 *
                                                                                                                                            W'.a₃ *
                                                                                                                                          W'.a₄ *
                                                                                                                                        P
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      Q
                                                                                                                                          (2 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        4 -
                                                                                                                                  W'.a₁ ^
                                                                                                                                            2 *
                                                                                                                                          W'.a₂ *
                                                                                                                                        W'.a₃ ^
                                                                                                                                          2 *
                                                                                                                                      P
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    Q
                                                                                                                                        (2 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      4 -
                                                                                                                                5 *
                                                                                                                                          W'.a₁ ^
                                                                                                                                            2 *
                                                                                                                                        W'.a₂ *
                                                                                                                                      W'.a₆ *
                                                                                                                                    P
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  Q
                                                                                                                                      (2 :
                                                                                                                                        Fin
                                                                                                                                          3) ^
                                                                                                                                    4 +
                                                                                                                              W'.a₁ ^
                                                                                                                                      2 *
                                                                                                                                    W'.a₄ ^
                                                                                                                                      2 *
                                                                                                                                  P
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                Q
                                                                                                                                    (2 :
                                                                                                                                      Fin
                                                                                                                                        3) ^
                                                                                                                                  4 +
                                                                                                                            W'.a₁ *
                                                                                                                                      W'.a₂ *
                                                                                                                                    W'.a₃ *
                                                                                                                                  W'.a₄ *
                                                                                                                                P
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                4 -
                                                                                                                          6 *
                                                                                                                                    W'.a₁ *
                                                                                                                                  W'.a₃ *
                                                                                                                                W'.a₆ *
                                                                                                                              P
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) *
                                                                                                                            Q
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              4 -
                                                                                                                        W'.a₂ ^
                                                                                                                                2 *
                                                                                                                              W'.a₃ ^
                                                                                                                                2 *
                                                                                                                            P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) *
                                                                                                                          Q
                                                                                                                              (2 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            4 -
                                                                                                                      4 *
                                                                                                                              W'.a₂ ^
                                                                                                                                2 *
                                                                                                                            W'.a₆ *
                                                                                                                          P
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) *
                                                                                                                        Q
                                                                                                                            (2 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          4 +
                                                                                                                    W'.a₂ *
                                                                                                                          W'.a₄ ^
                                                                                                                            2 *
                                                                                                                        P
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      Q
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        4 -
                                                                                                                  3 *
                                                                                                                          W'.a₄ *
                                                                                                                        W'.a₆ *
                                                                                                                      P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      4 -
                                                                                                                W'.a₁ ^
                                                                                                                        3 *
                                                                                                                      P
                                                                                                                        (1 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      3 *
                                                                                                                  Q
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) -
                                                                                                              W'.a₁ *
                                                                                                                      W'.a₂ *
                                                                                                                    P
                                                                                                                      (1 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    3 *
                                                                                                                Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) -
                                                                                                            3 *
                                                                                                                      W'.a₁ ^
                                                                                                                        2 *
                                                                                                                    P
                                                                                                                      (1 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) ^
                                                                                                                    2 *
                                                                                                                Q
                                                                                                                  (1 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) -
                                                                                                          3 *
                                                                                                                    W'.a₁ ^
                                                                                                                      2 *
                                                                                                                  W'.a₃ *
                                                                                                                P
                                                                                                                  (1 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                2 *
                                                                                                            Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              2 -
                                                                                                        3 *
                                                                                                                  W'.a₁ *
                                                                                                                W'.a₄ *
                                                                                                              P
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              2 *
                                                                                                          Q
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 -
                                                                                                      3 *
                                                                                                                W'.a₁ *
                                                                                                              P
                                                                                                                (1 :
                                                                                                                  Fin
                                                                                                                    3) *
                                                                                                            Q
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                              (1 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 *
                                                                                                        Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) -
                                                                                                    3 *
                                                                                                                W'.a₁ *
                                                                                                              W'.a₃ *
                                                                                                            P
                                                                                                              (1 :
                                                                                                                Fin
                                                                                                                  3) *
                                                                                                          Q
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) *
                                                                                                        Q
                                                                                                          (1 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      Q
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        2 -
                                                                                                  3 *
                                                                                                            W'.a₁ *
                                                                                                          W'.a₃ ^
                                                                                                            2 *
                                                                                                        P
                                                                                                          (1 :
                                                                                                            Fin
                                                                                                              3) *
                                                                                                      Q
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      3 -
                                                                                                9 *
                                                                                                          W'.a₁ *
                                                                                                        W'.a₆ *
                                                                                                      P
                                                                                                        (1 :
                                                                                                          Fin
                                                                                                            3) *
                                                                                                    Q
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) *
                                                                                                  Q
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    3 -
                                                                                              W'.a₁ ^
                                                                                                      3 *
                                                                                                    W'.a₆ *
                                                                                                  P
                                                                                                    (1 :
                                                                                                      Fin
                                                                                                        3) *
                                                                                                Q
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  4 +
                                                                                            W'.a₁ ^
                                                                                                      2 *
                                                                                                    W'.a₃ *
                                                                                                  W'.a₄ *
                                                                                                P
                                                                                                  (1 :
                                                                                                    Fin
                                                                                                      3) *
                                                                                              Q
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                4 -
                                                                                          W'.a₁ *
                                                                                                  W'.a₂ *
                                                                                                W'.a₃ ^
                                                                                                  2 *
                                                                                              P
                                                                                                (1 :
                                                                                                  Fin
                                                                                                    3) *
                                                                                            Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              4 -
                                                                                        4 * W'.a₁ *
                                                                                                W'.a₂ *
                                                                                              W'.a₆ *
                                                                                            P
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            4 +
                                                                                      W'.a₁ *
                                                                                            W'.a₄ ^
                                                                                              2 *
                                                                                          P
                                                                                            (1 :
                                                                                              Fin
                                                                                                3) *
                                                                                        Q
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          4 -
                                                                                    W'.a₁ ^ 2 *
                                                                                          W'.a₂ *
                                                                                        P
                                                                                          (2 :
                                                                                            Fin 3) *
                                                                                      Q
                                                                                          (0 :
                                                                                            Fin 3) ^
                                                                                        4 -
                                                                                  W'.a₂ ^ 2 *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) ^
                                                                                      4 -
                                                                                3 * W'.a₁ * W'.a₂ *
                                                                                      P
                                                                                        (2 :
                                                                                          Fin 3) *
                                                                                    Q (0 : Fin 3) ^
                                                                                      3 *
                                                                                  Q (1 : Fin 3) -
                                                                              W'.a₁ ^ 3 * W'.a₃ *
                                                                                    P (2 : Fin 3) *
                                                                                  Q (0 : Fin 3) ^
                                                                                    3 *
                                                                                Q (2 : Fin 3) -
                                                                            W'.a₁ ^ 2 * W'.a₄ *
                                                                                  P (2 : Fin 3) *
                                                                                Q (0 : Fin 3) ^ 3 *
                                                                              Q (2 : Fin 3) -
                                                                          4 * W'.a₁ * W'.a₂ *
                                                                                  W'.a₃ *
                                                                                P (2 : Fin 3) *
                                                                              Q (0 : Fin 3) ^ 3 *
                                                                            Q (2 : Fin 3) -
                                                                        4 * W'.a₂ * W'.a₄ *
                                                                              P (2 : Fin 3) *
                                                                            Q (0 : Fin 3) ^ 3 *
                                                                          Q (2 : Fin 3) -
                                                                      3 * W'.a₂ * P (2 : Fin 3) *
                                                                          Q (0 : Fin 3) ^ 2 *
                                                                        Q (1 : Fin 3) ^ 2 -
                                                                    3 * W'.a₁ ^ 2 * W'.a₃ *
                                                                            P (2 : Fin 3) *
                                                                          Q (0 : Fin 3) ^ 2 *
                                                                        Q (1 : Fin 3) *
                                                                      Q (2 : Fin 3) -
                                                                  3 * W'.a₁ * W'.a₄ *
                                                                          P (2 : Fin 3) *
                                                                        Q (0 : Fin 3) ^ 2 *
                                                                      Q (1 : Fin 3) *
                                                                    Q (2 : Fin 3) -
                                                                3 * W'.a₂ * W'.a₃ * P (2 : Fin 3) *
                                                                      Q (0 : Fin 3) ^ 2 *
                                                                    Q (1 : Fin 3) *
                                                                  Q (2 : Fin 3) -
                                                              3 * W'.a₁ ^ 2 * W'.a₃ ^ 2 *
                                                                    P (2 : Fin 3) *
                                                                  Q (0 : Fin 3) ^ 2 *
                                                                Q (2 : Fin 3) ^ 2 -
                                                            6 * W'.a₁ * W'.a₃ * W'.a₄ *
                                                                  P (2 : Fin 3) *
                                                                Q (0 : Fin 3) ^ 2 *
                                                              Q (2 : Fin 3) ^ 2 -
                                                          3 * W'.a₂ * W'.a₃ ^ 2 * P (2 : Fin 3) *
                                                              Q (0 : Fin 3) ^ 2 *
                                                            Q (2 : Fin 3) ^ 2 -
                                                        9 * W'.a₂ * W'.a₆ * P (2 : Fin 3) *
                                                            Q (0 : Fin 3) ^ 2 *
                                                          Q (2 : Fin 3) ^ 2 -
                                                      3 * W'.a₄ ^ 2 * P (2 : Fin 3) *
                                                          Q (0 : Fin 3) ^ 2 *
                                                        Q (2 : Fin 3) ^ 2 -
                                                    3 * W'.a₁ * W'.a₃ * P (2 : Fin 3) *
                                                          Q (0 : Fin 3) *
                                                        Q (1 : Fin 3) ^ 2 *
                                                      Q (2 : Fin 3) -
                                                  3 * W'.a₄ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                                      Q (1 : Fin 3) ^ 2 *
                                                    Q (2 : Fin 3) -
                                                3 * W'.a₁ * W'.a₃ ^ 2 * P (2 : Fin 3) *
                                                      Q (0 : Fin 3) *
                                                    Q (1 : Fin 3) *
                                                  Q (2 : Fin 3) ^ 2 -
                                              3 * W'.a₃ * W'.a₄ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                                  Q (1 : Fin 3) *
                                                Q (2 : Fin 3) ^ 2 -
                                            W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P (2 : Fin 3) *
                                                Q (0 : Fin 3) *
                                              Q (2 : Fin 3) ^ 3 +
                                          W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P (2 : Fin 3) *
                                              Q (0 : Fin 3) *
                                            Q (2 : Fin 3) ^ 3 -
                                        3 * W'.a₁ * W'.a₃ ^ 3 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                          Q (2 : Fin 3) ^ 3 -
                                      9 * W'.a₁ * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                        Q (2 : Fin 3) ^ 3 -
                                    W'.a₂ ^ 2 * W'.a₃ ^ 2 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                      Q (2 : Fin 3) ^ 3 -
                                  4 * W'.a₂ ^ 2 * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                    Q (2 : Fin 3) ^ 3 +
                                W'.a₂ * W'.a₄ ^ 2 * P (2 : Fin 3) * Q (0 : Fin 3) *
                                  Q (2 : Fin 3) ^ 3 -
                              3 * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) * Q (0 : Fin 3) *
                                Q (2 : Fin 3) ^ 3 -
                            9 * W'.a₄ * W'.a₆ * P (2 : Fin 3) * Q (0 : Fin 3) * Q (2 : Fin 3) ^ 3 -
                          W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
                        W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                      W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                    W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
                  4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
                2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
              W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 -
            4 * W'.a₂ * W'.a₄ * W'.a₆ * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4 +
          W'.a₄ ^ 3 * P (2 : Fin 3) * Q (2 : Fin 3) ^ 4) *
        (equation_iff P).mp hP +
      (3 * W'.a₁ ^ 2 * P (0 : Fin 3) ^ 4 * Q (0 : Fin 3) +
                                                                                                                                                          6 *
                                                                                                                                                                W'.a₂ *
                                                                                                                                                              P
                                                                                                                                                                  (0 :
                                                                                                                                                                    Fin
                                                                                                                                                                      3) ^
                                                                                                                                                                4 *
                                                                                                                                                            Q
                                                                                                                                                              (0 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) +
                                                                                                                                                        W'.a₁ ^
                                                                                                                                                              4 *
                                                                                                                                                            P
                                                                                                                                                                (0 :
                                                                                                                                                                  Fin
                                                                                                                                                                    3) ^
                                                                                                                                                              4 *
                                                                                                                                                          Q
                                                                                                                                                            (2 :
                                                                                                                                                              Fin
                                                                                                                                                                3) +
                                                                                                                                                      2 *
                                                                                                                                                              W'.a₁ ^
                                                                                                                                                                2 *
                                                                                                                                                            W'.a₂ *
                                                                                                                                                          P
                                                                                                                                                              (0 :
                                                                                                                                                                Fin
                                                                                                                                                                  3) ^
                                                                                                                                                            4 *
                                                                                                                                                        Q
                                                                                                                                                          (2 :
                                                                                                                                                            Fin
                                                                                                                                                              3) +
                                                                                                                                                    6 *
                                                                                                                                                            W'.a₁ *
                                                                                                                                                          W'.a₃ *
                                                                                                                                                        P
                                                                                                                                                            (0 :
                                                                                                                                                              Fin
                                                                                                                                                                3) ^
                                                                                                                                                          4 *
                                                                                                                                                      Q
                                                                                                                                                        (2 :
                                                                                                                                                          Fin
                                                                                                                                                            3) +
                                                                                                                                                  W'.a₂ ^
                                                                                                                                                        2 *
                                                                                                                                                      P
                                                                                                                                                          (0 :
                                                                                                                                                            Fin
                                                                                                                                                              3) ^
                                                                                                                                                        4 *
                                                                                                                                                    Q
                                                                                                                                                      (2 :
                                                                                                                                                        Fin
                                                                                                                                                          3) +
                                                                                                                                                3 *
                                                                                                                                                      W'.a₄ *
                                                                                                                                                    P
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) ^
                                                                                                                                                      4 *
                                                                                                                                                  Q
                                                                                                                                                    (2 :
                                                                                                                                                      Fin
                                                                                                                                                        3) +
                                                                                                                                              9 *
                                                                                                                                                      W'.a₁ *
                                                                                                                                                    P
                                                                                                                                                        (0 :
                                                                                                                                                          Fin
                                                                                                                                                            3) ^
                                                                                                                                                      3 *
                                                                                                                                                  P
                                                                                                                                                    (1 :
                                                                                                                                                      Fin
                                                                                                                                                        3) *
                                                                                                                                                Q
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) +
                                                                                                                                            4 *
                                                                                                                                                    W'.a₁ ^
                                                                                                                                                      3 *
                                                                                                                                                  P
                                                                                                                                                      (0 :
                                                                                                                                                        Fin
                                                                                                                                                          3) ^
                                                                                                                                                    3 *
                                                                                                                                                P
                                                                                                                                                  (1 :
                                                                                                                                                    Fin
                                                                                                                                                      3) *
                                                                                                                                              Q
                                                                                                                                                (2 :
                                                                                                                                                  Fin
                                                                                                                                                    3) +
                                                                                                                                          4 *
                                                                                                                                                    W'.a₁ *
                                                                                                                                                  W'.a₂ *
                                                                                                                                                P
                                                                                                                                                    (0 :
                                                                                                                                                      Fin
                                                                                                                                                        3) ^
                                                                                                                                                  3 *
                                                                                                                                              P
                                                                                                                                                (1 :
                                                                                                                                                  Fin
                                                                                                                                                    3) *
                                                                                                                                            Q
                                                                                                                                              (2 :
                                                                                                                                                Fin
                                                                                                                                                  3) +
                                                                                                                                        W'.a₁ ^
                                                                                                                                                  2 *
                                                                                                                                                W'.a₂ *
                                                                                                                                              P
                                                                                                                                                  (0 :
                                                                                                                                                    Fin
                                                                                                                                                      3) ^
                                                                                                                                                3 *
                                                                                                                                            P
                                                                                                                                              (2 :
                                                                                                                                                Fin
                                                                                                                                                  3) *
                                                                                                                                          Q
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) +
                                                                                                                                      9 *
                                                                                                                                                W'.a₁ *
                                                                                                                                              W'.a₃ *
                                                                                                                                            P
                                                                                                                                                (0 :
                                                                                                                                                  Fin
                                                                                                                                                    3) ^
                                                                                                                                              3 *
                                                                                                                                          P
                                                                                                                                            (2 :
                                                                                                                                              Fin
                                                                                                                                                3) *
                                                                                                                                        Q
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) +
                                                                                                                                    4 *
                                                                                                                                            W'.a₂ ^
                                                                                                                                              2 *
                                                                                                                                          P
                                                                                                                                              (0 :
                                                                                                                                                Fin
                                                                                                                                                  3) ^
                                                                                                                                            3 *
                                                                                                                                        P
                                                                                                                                          (2 :
                                                                                                                                            Fin
                                                                                                                                              3) *
                                                                                                                                      Q
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) +
                                                                                                                                  9 *
                                                                                                                                          W'.a₄ *
                                                                                                                                        P
                                                                                                                                            (0 :
                                                                                                                                              Fin
                                                                                                                                                3) ^
                                                                                                                                          3 *
                                                                                                                                      P
                                                                                                                                        (2 :
                                                                                                                                          Fin
                                                                                                                                            3) *
                                                                                                                                    Q
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) +
                                                                                                                                4 *
                                                                                                                                          W'.a₁ ^
                                                                                                                                            3 *
                                                                                                                                        W'.a₃ *
                                                                                                                                      P
                                                                                                                                          (0 :
                                                                                                                                            Fin
                                                                                                                                              3) ^
                                                                                                                                        3 *
                                                                                                                                    P
                                                                                                                                      (2 :
                                                                                                                                        Fin
                                                                                                                                          3) *
                                                                                                                                  Q
                                                                                                                                    (2 :
                                                                                                                                      Fin
                                                                                                                                        3) +
                                                                                                                              4 *
                                                                                                                                        W'.a₁ ^
                                                                                                                                          2 *
                                                                                                                                      W'.a₄ *
                                                                                                                                    P
                                                                                                                                        (0 :
                                                                                                                                          Fin
                                                                                                                                            3) ^
                                                                                                                                      3 *
                                                                                                                                  P
                                                                                                                                    (2 :
                                                                                                                                      Fin
                                                                                                                                        3) *
                                                                                                                                Q
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) +
                                                                                                                            10 *
                                                                                                                                        W'.a₁ *
                                                                                                                                      W'.a₂ *
                                                                                                                                    W'.a₃ *
                                                                                                                                  P
                                                                                                                                      (0 :
                                                                                                                                        Fin
                                                                                                                                          3) ^
                                                                                                                                    3 *
                                                                                                                                P
                                                                                                                                  (2 :
                                                                                                                                    Fin
                                                                                                                                      3) *
                                                                                                                              Q
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) +
                                                                                                                          7 *
                                                                                                                                    W'.a₂ *
                                                                                                                                  W'.a₄ *
                                                                                                                                P
                                                                                                                                    (0 :
                                                                                                                                      Fin
                                                                                                                                        3) ^
                                                                                                                                  3 *
                                                                                                                              P
                                                                                                                                (2 :
                                                                                                                                  Fin
                                                                                                                                    3) *
                                                                                                                            Q
                                                                                                                              (2 :
                                                                                                                                Fin
                                                                                                                                  3) +
                                                                                                                        9 *
                                                                                                                              P
                                                                                                                                  (0 :
                                                                                                                                    Fin
                                                                                                                                      3) ^
                                                                                                                                2 *
                                                                                                                            P
                                                                                                                                (1 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 *
                                                                                                                          Q
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) +
                                                                                                                      6 *
                                                                                                                              W'.a₁ ^
                                                                                                                                2 *
                                                                                                                            P
                                                                                                                                (0 :
                                                                                                                                  Fin
                                                                                                                                    3) ^
                                                                                                                              2 *
                                                                                                                          P
                                                                                                                              (1 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 *
                                                                                                                        Q
                                                                                                                          (2 :
                                                                                                                            Fin
                                                                                                                              3) +
                                                                                                                    3 *
                                                                                                                            W'.a₂ *
                                                                                                                          P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 *
                                                                                                                        P
                                                                                                                            (1 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 *
                                                                                                                      Q
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) +
                                                                                                                  9 *
                                                                                                                            W'.a₃ *
                                                                                                                          P
                                                                                                                              (0 :
                                                                                                                                Fin
                                                                                                                                  3) ^
                                                                                                                            2 *
                                                                                                                        P
                                                                                                                          (1 :
                                                                                                                            Fin
                                                                                                                              3) *
                                                                                                                      P
                                                                                                                        (2 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    Q
                                                                                                                      (0 :
                                                                                                                        Fin
                                                                                                                          3) +
                                                                                                                3 *
                                                                                                                            W'.a₁ ^
                                                                                                                              2 *
                                                                                                                          W'.a₃ *
                                                                                                                        P
                                                                                                                            (0 :
                                                                                                                              Fin
                                                                                                                                3) ^
                                                                                                                          2 *
                                                                                                                      P
                                                                                                                        (1 :
                                                                                                                          Fin
                                                                                                                            3) *
                                                                                                                    P
                                                                                                                      (2 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  Q
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) +
                                                                                                              3 *
                                                                                                                          W'.a₁ *
                                                                                                                        W'.a₄ *
                                                                                                                      P
                                                                                                                          (0 :
                                                                                                                            Fin
                                                                                                                              3) ^
                                                                                                                        2 *
                                                                                                                    P
                                                                                                                      (1 :
                                                                                                                        Fin
                                                                                                                          3) *
                                                                                                                  P
                                                                                                                    (2 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                Q
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) +
                                                                                                            3 *
                                                                                                                        W'.a₂ *
                                                                                                                      W'.a₃ *
                                                                                                                    P
                                                                                                                        (0 :
                                                                                                                          Fin
                                                                                                                            3) ^
                                                                                                                      2 *
                                                                                                                  P
                                                                                                                    (1 :
                                                                                                                      Fin
                                                                                                                        3) *
                                                                                                                P
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) *
                                                                                                              Q
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) +
                                                                                                          3 *
                                                                                                                      W'.a₁ *
                                                                                                                    W'.a₂ *
                                                                                                                  W'.a₃ *
                                                                                                                P
                                                                                                                    (0 :
                                                                                                                      Fin
                                                                                                                        3) ^
                                                                                                                  2 *
                                                                                                              P
                                                                                                                  (2 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                2 *
                                                                                                            Q
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) +
                                                                                                        6 *
                                                                                                                  W'.a₂ *
                                                                                                                W'.a₄ *
                                                                                                              P
                                                                                                                  (0 :
                                                                                                                    Fin
                                                                                                                      3) ^
                                                                                                                2 *
                                                                                                            P
                                                                                                                (2 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              2 *
                                                                                                          Q
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) +
                                                                                                      9 *
                                                                                                              W'.a₃ ^
                                                                                                                2 *
                                                                                                            P
                                                                                                                (0 :
                                                                                                                  Fin
                                                                                                                    3) ^
                                                                                                              2 *
                                                                                                          P
                                                                                                              (2 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 *
                                                                                                        Q
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) +
                                                                                                    27 *
                                                                                                            W'.a₆ *
                                                                                                          P
                                                                                                              (0 :
                                                                                                                Fin
                                                                                                                  3) ^
                                                                                                            2 *
                                                                                                        P
                                                                                                            (2 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          2 *
                                                                                                      Q
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) +
                                                                                                  6 *
                                                                                                            W'.a₁ ^
                                                                                                              2 *
                                                                                                          W'.a₃ ^
                                                                                                            2 *
                                                                                                        P
                                                                                                            (0 :
                                                                                                              Fin
                                                                                                                3) ^
                                                                                                          2 *
                                                                                                      P
                                                                                                          (2 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        2 *
                                                                                                    Q
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) +
                                                                                                9 *
                                                                                                          W'.a₁ ^
                                                                                                            2 *
                                                                                                        W'.a₆ *
                                                                                                      P
                                                                                                          (0 :
                                                                                                            Fin
                                                                                                              3) ^
                                                                                                        2 *
                                                                                                    P
                                                                                                        (2 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      2 *
                                                                                                  Q
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) +
                                                                                              12 *
                                                                                                          W'.a₁ *
                                                                                                        W'.a₃ *
                                                                                                      W'.a₄ *
                                                                                                    P
                                                                                                        (0 :
                                                                                                          Fin
                                                                                                            3) ^
                                                                                                      2 *
                                                                                                  P
                                                                                                      (2 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    2 *
                                                                                                Q
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) +
                                                                                            3 *
                                                                                                      W'.a₂ *
                                                                                                    W'.a₃ ^
                                                                                                      2 *
                                                                                                  P
                                                                                                      (0 :
                                                                                                        Fin
                                                                                                          3) ^
                                                                                                    2 *
                                                                                                P
                                                                                                    (2 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  2 *
                                                                                              Q
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) +
                                                                                          9 *
                                                                                                    W'.a₂ *
                                                                                                  W'.a₆ *
                                                                                                P
                                                                                                    (0 :
                                                                                                      Fin
                                                                                                        3) ^
                                                                                                  2 *
                                                                                              P
                                                                                                  (2 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                2 *
                                                                                            Q
                                                                                              (2 :
                                                                                                Fin
                                                                                                  3) +
                                                                                        6 *
                                                                                                W'.a₄ ^
                                                                                                  2 *
                                                                                              P
                                                                                                  (0 :
                                                                                                    Fin
                                                                                                      3) ^
                                                                                                2 *
                                                                                            P
                                                                                                (2 :
                                                                                                  Fin
                                                                                                    3) ^
                                                                                              2 *
                                                                                          Q
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) +
                                                                                      3 * W'.a₁ *
                                                                                            P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          P
                                                                                              (1 :
                                                                                                Fin
                                                                                                  3) ^
                                                                                            3 *
                                                                                        Q
                                                                                          (2 :
                                                                                            Fin 3) +
                                                                                    9 * W'.a₁ *
                                                                                              W'.a₆ *
                                                                                            P
                                                                                              (0 :
                                                                                                Fin
                                                                                                  3) *
                                                                                          P
                                                                                            (1 :
                                                                                              Fin
                                                                                                3) *
                                                                                        P
                                                                                            (2 :
                                                                                              Fin
                                                                                                3) ^
                                                                                          2 *
                                                                                      Q
                                                                                        (2 :
                                                                                          Fin 3) +
                                                                                  3 * W'.a₁ ^ 2 *
                                                                                          W'.a₆ *
                                                                                        P
                                                                                          (0 :
                                                                                            Fin 3) *
                                                                                      P
                                                                                          (2 :
                                                                                            Fin 3) ^
                                                                                        3 *
                                                                                    Q (0 : Fin 3) -
                                                                                3 * W'.a₁ * W'.a₃ *
                                                                                        W'.a₄ *
                                                                                      P
                                                                                        (0 :
                                                                                          Fin 3) *
                                                                                    P (2 : Fin 3) ^
                                                                                      3 *
                                                                                  Q (0 : Fin 3) +
                                                                              6 * W'.a₂ *
                                                                                      W'.a₃ ^ 2 *
                                                                                    P (0 : Fin 3) *
                                                                                  P (2 : Fin 3) ^
                                                                                    3 *
                                                                                Q (0 : Fin 3) +
                                                                            24 * W'.a₂ * W'.a₆ *
                                                                                  P (0 : Fin 3) *
                                                                                P (2 : Fin 3) ^ 3 *
                                                                              Q (0 : Fin 3) -
                                                                          3 * W'.a₄ ^ 2 *
                                                                                P (0 : Fin 3) *
                                                                              P (2 : Fin 3) ^ 3 *
                                                                            Q (0 : Fin 3) +
                                                                        W'.a₁ ^ 4 * W'.a₆ *
                                                                              P (0 : Fin 3) *
                                                                            P (2 : Fin 3) ^ 3 *
                                                                          Q (2 : Fin 3) -
                                                                      W'.a₁ ^ 3 * W'.a₃ * W'.a₄ *
                                                                            P (0 : Fin 3) *
                                                                          P (2 : Fin 3) ^ 3 *
                                                                        Q (2 : Fin 3) +
                                                                    W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2 *
                                                                          P (0 : Fin 3) *
                                                                        P (2 : Fin 3) ^ 3 *
                                                                      Q (2 : Fin 3) +
                                                                  5 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ *
                                                                        P (0 : Fin 3) *
                                                                      P (2 : Fin 3) ^ 3 *
                                                                    Q (2 : Fin 3) -
                                                                W'.a₁ ^ 2 * W'.a₄ ^ 2 *
                                                                      P (0 : Fin 3) *
                                                                    P (2 : Fin 3) ^ 3 *
                                                                  Q (2 : Fin 3) -
                                                              W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ *
                                                                    P (0 : Fin 3) *
                                                                  P (2 : Fin 3) ^ 3 *
                                                                Q (2 : Fin 3) +
                                                            3 * W'.a₁ * W'.a₃ ^ 3 * P (0 : Fin 3) *
                                                                P (2 : Fin 3) ^ 3 *
                                                              Q (2 : Fin 3) +
                                                          15 * W'.a₁ * W'.a₃ * W'.a₆ *
                                                                P (0 : Fin 3) *
                                                              P (2 : Fin 3) ^ 3 *
                                                            Q (2 : Fin 3) +
                                                        W'.a₂ ^ 2 * W'.a₃ ^ 2 * P (0 : Fin 3) *
                                                            P (2 : Fin 3) ^ 3 *
                                                          Q (2 : Fin 3) +
                                                      4 * W'.a₂ ^ 2 * W'.a₆ * P (0 : Fin 3) *
                                                          P (2 : Fin 3) ^ 3 *
                                                        Q (2 : Fin 3) -
                                                    W'.a₂ * W'.a₄ ^ 2 * P (0 : Fin 3) *
                                                        P (2 : Fin 3) ^ 3 *
                                                      Q (2 : Fin 3) +
                                                  3 * W'.a₃ ^ 2 * W'.a₄ * P (0 : Fin 3) *
                                                      P (2 : Fin 3) ^ 3 *
                                                    Q (2 : Fin 3) +
                                                12 * W'.a₄ * W'.a₆ * P (0 : Fin 3) *
                                                    P (2 : Fin 3) ^ 3 *
                                                  Q (2 : Fin 3) +
                                              W'.a₁ ^ 3 * W'.a₆ * P (1 : Fin 3) *
                                                  P (2 : Fin 3) ^ 3 *
                                                Q (2 : Fin 3) -
                                            W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P (1 : Fin 3) *
                                                P (2 : Fin 3) ^ 3 *
                                              Q (2 : Fin 3) +
                                          W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P (1 : Fin 3) *
                                              P (2 : Fin 3) ^ 3 *
                                            Q (2 : Fin 3) +
                                        4 * W'.a₁ * W'.a₂ * W'.a₆ * P (1 : Fin 3) *
                                            P (2 : Fin 3) ^ 3 *
                                          Q (2 : Fin 3) -
                                      W'.a₁ * W'.a₄ ^ 2 * P (1 : Fin 3) * P (2 : Fin 3) ^ 3 *
                                        Q (2 : Fin 3) +
                                    W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) -
                                  W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P (2 : Fin 3) ^ 4 *
                                    Q (0 : Fin 3) +
                                W'.a₂ ^ 2 * W'.a₃ ^ 2 * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) +
                              4 * W'.a₂ ^ 2 * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) -
                            W'.a₂ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 4 * Q (0 : Fin 3) +
                          W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
                        W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                      W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                    W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
                  4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
                2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
              W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) +
            4 * W'.a₂ * W'.a₄ * W'.a₆ * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3) -
          W'.a₄ ^ 3 * P (2 : Fin 3) ^ 4 * Q (2 : Fin 3)) *
        (equation_iff Q).mp hQ


-- @@ L532-532 verbatim
end Projective


-- @@ L534-534 verbatim
end WeierstrassCurve


-- @@ L536-542 verbatim
/-! ## T-W7.0c-c5α skeleton: the residue-field vanishing principle

The on-curve identity for law 2 (c5) is NOT certified (cofactors ≈ 4–8k terms — over the
no-`maxHeartbeats` bar); per the certificate policy it factors through reducedness: an element
of a reduced Jacobson ring vanishing in every residue field at maximal ideals is zero. This is
the engine of the factorization bridge (board ticket T-W7.0c-c5α); the per-chart vanishing
statements land with c5α itself (they need the `E_U ×_U E_U` chart rings). -/


-- @@ L544-551 verbatim
/-- An element of a reduced Jacobson ring lying in every maximal ideal is zero (equivalently:
vanishing in every residue field kills it). Engine for T-W7.0c-c5α. -/
theorem eq_zero_of_forall_isMaximal_mem {A : Type*} [CommRing A] [IsJacobsonRing A]
    [IsReduced A] {a : A} (h : ∀ I : Ideal A, I.IsMaximal → a ∈ I) : a = 0 := by
  have hj : a ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.mpr fun _ hJ => h _ hJ.2
  rw [← Ideal.radical_eq_jacobson] at hj
  have hn : a ∈ nilradical A := hj
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at hn
