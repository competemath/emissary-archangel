import OAI.Computability.Superstring.WalkOutput


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring

-- @@ L6-6 verbatim
open BitCode


-- @@ L8-14 verbatim
theorem bitsList_eq_encodeList {α : Type} [Coded α] (e : α → List Bool)
    (he : ∀ a, bits a = e a) (xs : List α) : bits xs = encodeList e xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change false :: (bits a ++ bits xs) = false :: (e a ++ encodeList e xs)
    rw [he,ih]


-- @@ L16-17 verbatim
theorem bitsSymbol_eq (s : Symbol) : bits s = encodeSymbol s :=
  bitsList_eq_encodeList _ (fun _ => rfl) s


-- @@ L19-20 verbatim
theorem bitsWord_eq (w : Word) : bits w = encodeWord w :=
  bitsList_eq_encodeList _ bitsSymbol_eq w


-- @@ L22-23 verbatim
theorem bitsInstance_eq (S : Instance) : bits S = encodeInstance S :=
  bitsList_eq_encodeList _ bitsWord_eq S


-- @@ L25-25 verbatim
def answer : Instance → Word := Executable.solve


-- @@ L27-32 verbatim
theorem answer_poly : Poly answer := by
  unfold answer
  apply Executable.poly_solve
  convert (Poly.ltList (α:=Bool) Poly.ltBool) using 1
  funext q
  exact decide_eq_decide.mpr Iff.rfl


-- @@ L34-40 verbatim
theorem answer_implementation : HasPolynomialImplementation answer := by
  have hc := RunsInPolyTime.certificate answer_poly
  have hi : (bits : Instance → List Bool) = encodeInstance := funext bitsInstance_eq
  have ho : (bits : Word → List Bool) = encodeWord := funext bitsWord_eq
  change ∃ M : Turing.TM2ComputableInPolyTime bits bits answer, ∀ k : M.tm.K, Finite (M.tm.Γ k) at hc
  rw [hi,ho] at hc
  exact hc


-- @@ L42-46 verbatim
theorem weight_le_opt_with (S : Instance) (d : DecidableEq Symbol) :
    @Counts.Data.weight Symbol d inferInstance (@Input.data Symbol d S) ≤ opt S := by
  have he : d = @instDecidableEqList Bool instDecidableEqBool := Subsingleton.elim _ _
  rw [he]
  exact weight_le_opt S


-- @@ L48-53 verbatim
theorem answer_spec (S : Instance) : IsCommonSuperstring S (answer S) ∧
    (answer S).length ≤ 2*opt S := by
  obtain ⟨ht,hl⟩ := Executable.solve_spec S
  refine ⟨ht, ?_⟩
  apply hl.trans
  exact Nat.mul_le_mul_left 2 (weight_le_opt_with S LinearOrder.toDecidableEq)


-- @@ L55-60 verbatim
/-- The deterministic algorithm with its exact finite-alphabet bit-machine
certificate, contiguous coverage, and factor-two bound in symbols. -/
theorem main : ∃ f : Instance → Word,
    HasPolynomialImplementation f ∧
    ∀ S, IsCommonSuperstring S (f S) ∧ (f S).length ≤ 2 * opt S :=
  ⟨answer, answer_implementation, answer_spec⟩



-- @@ L63-63 verbatim
end Superstring


-- @@ L65-65 verbatim
end OAI
