import { splitStatementAndProof } from "../lib/stage-record.mjs";
// node scripts/test-stage-record.mjs — the statement/proof split of a verified script (exits 1 on a wrong split)
const cases = [
  ["def a := 1\ntheorem foo (h : x = y) : y = x := by\n  simp [h]", "foo", "theorem foo (h : x = y) : y = x", ":= by\n  simp [h]"],
  ["theorem binom_symm_of_le : ∀ n k, k ≤ n → f n k = f n (n - k)\n  | 0, 0, _ => rfl\n  | n + 1, k + 1, h => by\n      have hkn : k < n := by omega\n      exact hkn", "binom_symm_of_le", "theorem binom_symm_of_le : ∀ n k, k ≤ n → f n k = f n (n - k)", "| 0, 0, _ => rfl"],
  ["theorem bar {f : ℕ → ℕ} (h : ∀ x, f x = (fun y => y) x) : f 0 = 0 := h 0", "bar", "theorem bar {f : ℕ → ℕ} (h : ∀ x, f x = (fun y => y) x) : f 0 = 0", ":= h 0"],
  ["theorem baz : True -- a comment with := inside\n  := trivial", "baz", "theorem baz : True -- a comment with := inside", ":= trivial"],
  ["theorem q (s : Set ℕ) : s = {x | x ∈ s} := rfl", "q", "theorem q (s : Set ℕ) : s = {x | x ∈ s}", ":= rfl"],
  ["theorem abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) :\n    |B1 x| ≤ 1 / 2 := by\n  simp", "abs_B1_le_half", "theorem abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) :\n    |B1 x| ≤ 1 / 2", ":= by"],
  ["theorem len : ∀ t, (b t).length = t\n  | 0 => rfl\n  | t + 1 => by simpa", "len", "theorem len : ∀ t, (b t).length = t", "| 0 => rfl"],
];
let bad = 0;
for (const [text, name, st, prStart] of cases) {
  const r = splitStatementAndProof(text, name);
  const ok = r && r.statement === st && r.proof.startsWith(prStart);
  if (!ok) { bad++; console.log("FAIL", name, JSON.stringify(r)); } else console.log("ok", name);
}
process.exit(bad ? 1 : 0);
