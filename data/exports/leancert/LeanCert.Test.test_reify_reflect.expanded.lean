import LeanCert.Meta.ToExpr
import LeanCert.Tactic.IntervalAuto

-- Reflection smoke tests: these fail to compile if reification cannot parse the form.

-- @@ L5-5 verbatim
#leancert_reflect (fun x : Real => x + 1)

-- @@ L6-6 verbatim
#leancert_reflect (fun x : Real => x - 1)

-- @@ L7-7 verbatim
#leancert_reflect (fun x : Real => x / 2)

-- @@ L8-8 verbatim
#leancert_reflect (fun x : Real => abs x)

-- @@ L9-9 verbatim
#leancert_reflect (fun x : Real => x ^ ((1 : Real) / 2))

-- @@ L10-10 verbatim
#leancert_reflect (fun x : Real => x ^ ((2 : Real)⁻¹))

-- @@ L11-11 verbatim
#leancert_reflect (fun x : Real => x ^ ((3 : Real) / 2))

-- @@ L12-12 verbatim
#leancert_reflect (fun x : Real => x ^ (1.5 : Real))

-- @@ L13-13 verbatim
#leancert_reflect (fun x : Real => x ^ ((5 : Real) / 2))

-- @@ L14-14 verbatim
#leancert_reflect (fun x : Real => x ^ ((-1 : Real) / 2))

-- @@ L15-15 verbatim
#leancert_reflect (fun x : Real => x ^ ((-3 : Real) / 2))

-- @@ L16-16 verbatim
#leancert_reflect (fun x : Real => x ^ ((-2 : Real)))

-- @@ L17-17 verbatim
#leancert_reflect (fun x : Real => x ^ ((1 : Real) / 3))

-- @@ L18-18 verbatim
#leancert_reflect (fun x : Real => x ^ ((2 : Real) / 3))

-- @@ L19-19 verbatim
#leancert_reflect (fun x : Real => x ^ ((1 : Real) / 5))

-- @@ L20-20 verbatim
#leancert_reflect (fun x : Real => x ^ ((-2 : Real) / 3))

-- @@ L21-21 verbatim
#leancert_reflect (fun x : Real => Real.sinh x + Real.cosh x + Real.tanh x)

-- @@ L22-22 verbatim
#leancert_reflect (fun x : Real => max x (1 / 2 : Real))

-- @@ L23-23 verbatim
#leancert_reflect (fun x : Real => min x (1 / 2 : Real))

-- @@ L24-24 verbatim
#leancert_reflect (fun x : Real => x + Real.pi)

-- @@ L25-25 verbatim
#leancert_reflect (fun x : Real => x + Real.eulerMascheroniConstant)

-- @@ L26-26 verbatim
#leancert_reflect (fun x : Real => x + ((-2 : Int) : Real) + ((3 / 7 : Rat) : Real))


-- @@ L28-30 verbatim
theorem reify_norm_sub_div :
    ∀ x ∈ Set.Icc (1 : Real) 2, x - x / 2 ≤ (2 : Rat) := by
  certify_bound


-- @@ L32-34 verbatim
theorem reify_norm_casts :
    ∀ x ∈ Set.Icc (0 : Real) 1, x + ((1 : Nat) : Real) ≤ (2 : Rat) := by
  certify_bound


-- @@ L36-38 verbatim
theorem reify_norm_max :
    ∀ x ∈ Set.Icc (0 : Real) 1, max x (1 / 2 : Real) ≤ (2 : Rat) := by
  certify_bound


-- @@ L40-42 verbatim
theorem reify_norm_min :
    ∀ x ∈ Set.Icc (0 : Real) 1, (-1 : Rat) ≤ min x (1 / 2 : Real) := by
  certify_bound

-- @@ L43-45 verbatim
theorem reify_rpow_thirds_bound :
    ∀ x ∈ Set.Icc (2 : Real) 3, x ^ ((1 : Real) / 3) ≤ (2 : Rat) := by
  certify_bound


-- @@ L47-49 verbatim
theorem reify_rpow_neg_thirds_bound :
    ∀ x ∈ Set.Icc (2 : Real) 3, x ^ ((-2 : Real) / 3) ≤ (1 : Rat) := by
  certify_bound


-- @@ L51-53 verbatim
theorem reify_named_const_pi_bound :
    ∀ x ∈ Set.Icc (0 : Real) 1, x + Real.pi ≤ (5 : Rat) := by
  certify_bound
