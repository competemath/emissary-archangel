import BernoulliRegular.BernoulliFast.ValuesUpTo100
import BernoulliRegular.Main


-- @@ L4-18 verbatim
/-!
# Regularity of primes below 100

This file records the regularity status of each prime below `100`.

Regular primes below `100`:
`2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 61, 71, 73, 79,
83, 89, 97`.

Irregular primes below `100`:
`37, 59, 67`.

The computational Bernoulli steps are discharged by `norm_num` using the
`@[simp]` values from `BernoulliRegular.BernoulliFast.ValuesUpTo100`.
-/


-- @@ L20-20 verbatim
namespace BernoulliRegular


-- @@ L22-27 verbatim
private theorem regular_of_bernoulli_values
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hB : ∀ k, 1 ≤ k → 2 * k ≤ p - 3 →
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    IsRegularPrime p :=
  (kummer_criterion (p := p) hp_odd).mpr hB


-- @@ L29-34 verbatim
private theorem not_regular_of_dvd_bernoulli_value
    {p k : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hk : 1 ≤ k) (hk_range : 2 * k ≤ p - 3)
    (hdiv : (p : ℤ) ∣ (bernoulli (2 * k)).num) :
    ¬ IsRegularPrime p := fun hreg ↦
  ((kummer_criterion (p := p) hp_odd).mp hreg k hk hk_range) hdiv


-- @@ L36-41 verbatim
macro "regular_prime_by_values" p:num upper:num : tactic => `(tactic|
  (haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
   exact regular_of_bernoulli_values (p := $p) (by norm_num) (by
     intro k hk hk_range
     have hk_upper : k ≤ $upper := by omega
     interval_cases k <;> norm_num)))


-- @@ L43-46 verbatim
macro "irregular_prime_by_value" p:num k:num : tactic => `(tactic|
  (haveI : Fact (Nat.Prime $p) := ⟨by norm_num⟩
   exact not_regular_of_dvd_bernoulli_value (p := $p) (k := $k)
     (by norm_num) (by norm_num) (by norm_num) (by norm_num)))


-- @@ L48-49 verbatim
theorem isRegularPrime_two_lt100 : IsRegularPrime 2 :=
  isRegularPrime_two


-- @@ L51-54 verbatim
theorem isRegularPrime_three_lt100 :
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    IsRegularPrime 3 :=
  isRegularPrime_three


-- @@ L56-59 expanded
theorem isRegularPrime_five_lt100 :
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    IsRegularPrime 5 :=
  by
  ( haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 5) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 1 := by omega
          interval_cases k <;> norm_num))


-- @@ L61-64 expanded
theorem isRegularPrime_seven_lt100 :
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    IsRegularPrime 7 :=
  by
  ( haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 7) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 2 := by omega
          interval_cases k <;> norm_num))


-- @@ L66-69 expanded
theorem isRegularPrime_eleven_lt100 :
    letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    IsRegularPrime 11 :=
  by
  ( haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 11) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 4 := by omega
          interval_cases k <;> norm_num))


-- @@ L71-74 expanded
theorem isRegularPrime_thirteen_lt100 :
    letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    IsRegularPrime 13 :=
  by
  ( haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 13) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 5 := by omega
          interval_cases k <;> norm_num))


-- @@ L76-79 expanded
theorem isRegularPrime_seventeen_lt100 :
    letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    IsRegularPrime 17 :=
  by
  ( haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 17) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 7 := by omega
          interval_cases k <;> norm_num))


-- @@ L81-84 expanded
theorem isRegularPrime_nineteen_lt100 :
    letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    IsRegularPrime 19 :=
  by
  ( haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 19) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 8 := by omega
          interval_cases k <;> norm_num))


-- @@ L86-89 expanded
theorem isRegularPrime_twentythree_lt100 :
    letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    IsRegularPrime 23 :=
  by
  ( haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 23) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 10 := by omega
          interval_cases k <;> norm_num))


-- @@ L91-94 expanded
theorem isRegularPrime_twentynine_lt100 :
    letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    IsRegularPrime 29 :=
  by
  ( haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 29) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 13 := by omega
          interval_cases k <;> norm_num))


-- @@ L96-99 expanded
theorem isRegularPrime_thirtyone_lt100 :
    letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    IsRegularPrime 31 :=
  by
  ( haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 31) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 14 := by omega
          interval_cases k <;> norm_num))


-- @@ L101-104 expanded
theorem not_isRegularPrime_thirtyseven :
    letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    ¬IsRegularPrime 37 :=
  by
  ( haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    exact
      not_regular_of_dvd_bernoulli_value (p := 37) (k := 16) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))


-- @@ L106-109 expanded
theorem isRegularPrime_fortyone_lt100 :
    letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    IsRegularPrime 41 :=
  by
  ( haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 41) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 19 := by omega
          interval_cases k <;> norm_num))


-- @@ L111-114 expanded
theorem isRegularPrime_fortythree_lt100 :
    letI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    IsRegularPrime 43 :=
  by
  ( haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 43) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 20 := by omega
          interval_cases k <;> norm_num))


-- @@ L116-119 expanded
theorem isRegularPrime_fortyseven_lt100 :
    letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    IsRegularPrime 47 :=
  by
  ( haveI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 47) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 22 := by omega
          interval_cases k <;> norm_num))


-- @@ L121-124 expanded
theorem isRegularPrime_fiftythree_lt100 :
    letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    IsRegularPrime 53 :=
  by
  ( haveI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 53) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 25 := by omega
          interval_cases k <;> norm_num))


-- @@ L126-129 expanded
theorem not_isRegularPrime_fiftynine_lt100 :
    letI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    ¬IsRegularPrime 59 :=
  by
  ( haveI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    exact
      not_regular_of_dvd_bernoulli_value (p := 59) (k := 22) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))


-- @@ L131-134 expanded
theorem isRegularPrime_sixtyone_lt100 :
    letI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    IsRegularPrime 61 :=
  by
  ( haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 61) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 29 := by omega
          interval_cases k <;> norm_num))


-- @@ L136-139 expanded
theorem not_isRegularPrime_sixtyseven_lt100 :
    letI : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    ¬IsRegularPrime 67 :=
  by
  ( haveI : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact
      not_regular_of_dvd_bernoulli_value (p := 67) (k := 29) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))


-- @@ L141-144 expanded
theorem isRegularPrime_seventyone_lt100 :
    letI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    IsRegularPrime 71 :=
  by
  ( haveI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 71) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 34 := by omega
          interval_cases k <;> norm_num))


-- @@ L146-149 expanded
theorem isRegularPrime_seventythree_lt100 :
    letI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    IsRegularPrime 73 :=
  by
  ( haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 73) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 35 := by omega
          interval_cases k <;> norm_num))


-- @@ L151-154 expanded
theorem isRegularPrime_seventynine_lt100 :
    letI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    IsRegularPrime 79 :=
  by
  ( haveI : Fact (Nat.Prime 79) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 79) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 38 := by omega
          interval_cases k <;> norm_num))


-- @@ L156-159 expanded
theorem isRegularPrime_eightythree_lt100 :
    letI : Fact (Nat.Prime 83) := ⟨by norm_num⟩
    IsRegularPrime 83 :=
  by
  ( haveI : Fact (Nat.Prime 83) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 83) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 40 := by omega
          interval_cases k <;> norm_num))


-- @@ L161-164 expanded
theorem isRegularPrime_eightynine_lt100 :
    letI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
    IsRegularPrime 89 :=
  by
  ( haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 89) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 43 := by omega
          interval_cases k <;> norm_num))


-- @@ L166-169 expanded
theorem isRegularPrime_ninetyseven_lt100 :
    letI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
    IsRegularPrime 97 :=
  by
  ( haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
    exact
      regular_of_bernoulli_values (p := 97) (by norm_num)
        (by
          intro k hk hk_range
          have hk_upper : k ≤ 47 := by omega
          interval_cases k <;> norm_num))


-- @@ L171-204 verbatim
/-- Every prime below `100` except the three irregular primes `37`, `59`,
and `67` is regular. -/
theorem isRegularPrime_of_prime_lt100_of_ne_irregular
    {n : ℕ} (hn_prime : n.Prime) (hn_two : 2 < n) (hn_lt100 : n < 100)
    (hn37 : n ≠ 37) (hn59 : n ≠ 59) (hn67 : n ≠ 67) :
    letI : Fact n.Prime := ⟨hn_prime⟩
    IsRegularPrime n := by
  haveI : Fact n.Prime := ⟨hn_prime⟩
  interval_cases n <;> first
    | (exfalso; norm_num at hn_prime; done)
    | exact False.elim (hn37 rfl)
    | exact False.elim (hn59 rfl)
    | exact False.elim (hn67 rfl)
    | simpa using isRegularPrime_three_lt100
    | simpa using isRegularPrime_five_lt100
    | simpa using isRegularPrime_seven_lt100
    | simpa using isRegularPrime_eleven_lt100
    | simpa using isRegularPrime_thirteen_lt100
    | simpa using isRegularPrime_seventeen_lt100
    | simpa using isRegularPrime_nineteen_lt100
    | simpa using isRegularPrime_twentythree_lt100
    | simpa using isRegularPrime_twentynine_lt100
    | simpa using isRegularPrime_thirtyone_lt100
    | simpa using isRegularPrime_fortyone_lt100
    | simpa using isRegularPrime_fortythree_lt100
    | simpa using isRegularPrime_fortyseven_lt100
    | simpa using isRegularPrime_fiftythree_lt100
    | simpa using isRegularPrime_sixtyone_lt100
    | simpa using isRegularPrime_seventyone_lt100
    | simpa using isRegularPrime_seventythree_lt100
    | simpa using isRegularPrime_seventynine_lt100
    | simpa using isRegularPrime_eightythree_lt100
    | simpa using isRegularPrime_eightynine_lt100
    | simpa using isRegularPrime_ninetyseven_lt100


-- @@ L206-206 verbatim
end BernoulliRegular
