import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.PrimeChannels


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped TensorProduct

-- @@ L8-8 verbatim
open scoped InnerProductSpace

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Set Module

-- @@ L11-11 verbatim
open Topology

-- @@ L12-12 verbatim
open NormedSpace

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped ComplexOrder

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open NormedSpace

-- @@ L18-18 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L19-19 verbatim
open UniformSpace

-- @@ L20-20 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L21-21 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L22-22 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L24-24 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L25-25 verbatim
open Filter Topology

-- @@ L26-26 verbatim
open Topology

-- @@ L27-27 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L28-28 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L29-29 verbatim
open NormedSpace

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped ComplexOrder

-- @@ L32-32 verbatim
open scoped InnerProductSpace

-- @@ L33-33 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L34-34 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L35-35 verbatim
open UniformSpace


-- @@ L37-37 verbatim
namespace KirchbergRordam.StandardPrimeMultiplicity



-- @@ L40-42 verbatim
lemma copies_pos (p : ℕ) (hp : 2≤p) : 0<copies p := by
  unfold copies
  exact Nat.mul_pos (by omega) (by positivity)

-- @@ L43-46 verbatim
lemma dimension (p : ℕ) (hp : 2≤p) : p+p*(p+1)*copies p=next p := by
  cases p with
  | zero => omega
  | succ p => simp only [copies,next,Nat.add_sub_cancel]; ring

-- @@ L47-50 verbatim
lemma middle_add_one (p : ℕ) (hp : 2≤p) : middle p+1=p*(p+1)*(copies p)^2 := by
  have hc := copies_pos p hp
  unfold middle
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))

-- @@ L51-54 verbatim
lemma zero_low (p : ℕ) (hp : 2≤p) : (p+1)*lower p=next p+1 := by
  rw [←dimension p hp]
  unfold lower
  ring

-- @@ L55-58 verbatim
lemma one_low (p : ℕ) (hp : 2≤p) : p*upper p=next p := by
  rw [←dimension p hp]
  unfold upper
  ring

-- @@ L59-64 verbatim
lemma zero_mid (p : ℕ) (hp : 2≤p) : upper p+middle p=copies p*(next p+1) := by
  have he : (upper p+middle p)+1=copies p*(next p+1)+1 := by
    rw [add_assoc,middle_add_one p hp,←dimension p hp]
    unfold upper
    ring
  omega

-- @@ L65-70 verbatim
lemma one_mid (p : ℕ) (hp : 2≤p) : lower p+middle p=next p*copies p := by
  have he : (lower p+middle p)+1=next p*copies p+1 := by
    rw [add_assoc,middle_add_one p hp,←dimension p hp]
    unfold lower
    ring
  omega

-- @@ L71-71 verbatim
lemma lower_pos (p : ℕ) : 0<lower p := by unfold lower; omega

-- @@ L72-72 verbatim
lemma upper_pos (p : ℕ) : 0<upper p := by unfold upper; omega

-- @@ L73-74 verbatim
lemma next_two (p : ℕ) (hp : 2≤p) : 2≤next p := by
  exact hp.trans (Nat.le_self_pow (by decide) p)



-- @@ L77-77 verbatim
@[simp] lemma size_zero : size 0=2 := rfl

-- @@ L78-78 verbatim
@[simp] lemma size_succ (n : ℕ) : size (n+1)=next (size n) := rfl

-- @@ L79-82 verbatim
lemma size_two (n : ℕ) : 2 ≤ size n := by
  induction n with
  | zero => simp
  | succ n ih => exact next_two _ ih

-- @@ L83-86 verbatim
lemma size_power (n : ℕ) : size n=2^(7^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [size_succ,next,ih,←pow_mul,pow_succ]

-- @@ L87-88 verbatim
lemma size_coprime (n : ℕ) : (size n).Coprime (size n+1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

-- @@ L89-89 verbatim
end KirchbergRordam.StandardPrimeMultiplicity

-- @@ L90-90 verbatim
namespace KirchbergRordam.StandardPrimeModel

-- @@ L91-91 verbatim
open StandardPrimeMultiplicity

-- @@ L92-92 verbatim
def Algebra : Type := presentation.Algebra

-- @@ L93-93 verbatim
instance : CStarAlgebra Algebra := inferInstanceAs (CStarAlgebra presentation.Algebra)

-- @@ L94-94 verbatim
instance : Nontrivial Algebra := inferInstanceAs (Nontrivial presentation.Algebra)

-- @@ L95-96 verbatim
instance : TopologicalSpace.SeparableSpace Algebra :=
  inferInstanceAs (TopologicalSpace.SeparableSpace presentation.Algebra)

-- @@ L97-97 verbatim
end KirchbergRordam.StandardPrimeModel


-- @@ L99-99 verbatim
namespace KirchbergRordam.StandardPrimeMultiplicity


-- @@ L101-101 verbatim
def k₀ (p : ℕ) : ℕ := upper p

-- @@ L102-102 verbatim
def k₁ (p : ℕ) : ℕ := lower p

-- @@ L103-107 verbatim
lemma k₀_formula (p : ℕ) (hp : 2≤p) : k₀ p=p^6 := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0<p)
  change p*upper p=p*p^6
  rw [one_low p hp]
  simp [next,pow_succ,mul_comm]

-- @@ L108-110 verbatim
lemma next_factors (p : ℕ) (hp : 2≤p) :
    next p=p*k₀ p ∧ next p+1=(p+1)*k₁ p :=
  ⟨(one_low p hp).symm,(zero_low p hp).symm⟩

-- @@ L111-112 verbatim
lemma next_coprime (p : ℕ) : (next p).Coprime (next p+1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

-- @@ L113-116 verbatim
lemma multipliers_coprime (p : ℕ) (hp : 2≤p) : (k₀ p).Coprime (k₁ p) := by
  apply (next_coprime p).of_dvd
  · exact ⟨p,by rw [(next_factors p hp).1,mul_comm]⟩
  · exact ⟨p+1,by rw [(next_factors p hp).2,mul_comm]⟩

-- @@ L117-122 verbatim
lemma copies_ge_fourth (p : ℕ) (hp : 2≤p) : p^4≤copies p := by
  have h : 1≤p-1 := by omega
  calc
    p^4 ≤ p^4+p^2+1 := by omega
    _ = 1*(p^4+p^2+1) := (one_mul _).symm
    _ ≤ (p-1)*(p^4+p^2+1) := Nat.mul_le_mul_right _ h

-- @@ L123-127 verbatim
lemma fourth_large (p : ℕ) (hp : 2≤p) : 2*(p+1)<p^4 := by
  have h2 : 2*p≤p^2 := by nlinarith
  have h3 : 4≤p^2 := by nlinarith
  have h4 : 4*p^2≤p^4 := by nlinarith [sq_nonneg (p^2)]
  nlinarith

-- @@ L128-135 verbatim
lemma multiplier_growth (p : ℕ) (hp : 2≤p) :
    2*p*(p+1)<k₀ p ∧ 2*p*(p+1)<k₁ p := by
  have hc := (fourth_large p hp).trans_le (copies_ge_fourth p hp)
  constructor
  · change 2*p*(p+1)<(p+1)*copies p+1
    nlinarith
  · change 2*p*(p+1)<p*copies p+1
    nlinarith

-- @@ L136-142 verbatim
lemma total_slots (p : ℕ) (hp : 2≤p) :
    lower p+upper p+middle p=k₀ p*k₁ p := by
  have h : (lower p+upper p+middle p)+1=k₀ p*k₁ p+1 := by
    rw [add_assoc,middle_add_one p hp]
    unfold k₀ k₁ lower upper
    ring
  omega

-- @@ L143-147 verbatim
lemma zero_remainder_lt (p : ℕ) (hp : 2≤p) : lower p<next p+1 := by
  have h := lower_pos p
  rw [(next_factors p hp).2]
  change lower p<(p+1)*lower p
  nlinarith

-- @@ L148-152 verbatim
lemma one_remainder_lt (p : ℕ) (hp : 2≤p) : upper p<next p := by
  have h := upper_pos p
  rw [(next_factors p hp).1]
  change upper p<p*upper p
  nlinarith

-- @@ L153-158 verbatim
lemma zero_remainder (p : ℕ) (hp : 2≤p) :
    (k₀ p*k₁ p)%(next p+1)=lower p := by
  have he : k₀ p*k₁ p=lower p+copies p*(next p+1) := by
    rw [←total_slots p hp,add_assoc,zero_mid p hp]
  rw [he,Nat.add_mod]
  simp [Nat.mod_eq_of_lt (zero_remainder_lt p hp)]

-- @@ L159-165 verbatim
lemma one_remainder (p : ℕ) (hp : 2≤p) :
    (k₀ p*k₁ p)%next p=upper p := by
  have he : k₀ p*k₁ p=upper p+next p*copies p := by
    rw [←one_mid p hp]
    exact (total_slots p hp).symm.trans (by omega)
  rw [he,Nat.add_mod]
  simp [Nat.mod_eq_of_lt (one_remainder_lt p hp)]

-- @@ L166-170 verbatim
lemma middle_classical (p : ℕ) (hp : 2≤p) :
    middle p=k₀ p*k₁ p-(k₀ p*k₁ p)%(next p+1)-(k₀ p*k₁ p)%next p := by
  rw [zero_remainder p hp,one_remainder p hp]
  have h := total_slots p hp
  omega

-- @@ L171-171 verbatim
end KirchbergRordam.StandardPrimeMultiplicity

-- @@ L172-172 verbatim
end


-- @@ L174-174 verbatim
end OAI
