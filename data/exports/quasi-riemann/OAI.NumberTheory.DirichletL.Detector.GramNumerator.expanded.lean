import OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
import OAI.NumberTheory.DirichletL.Detector.GramMean


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L13-14 verbatim
def numeratorExtension (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) : O→*ℂ :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr


-- @@ L16-19 verbatim
lemma numeratorExtension_norm (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n : O) :
    ‖numeratorExtension u a b r hr n‖≤1 := by
  rw [numeratorExtension,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (numeratorBadTwist_norm _ _ _ _ _ _)).trans (movingNumeratorRow_norm _ _ _)


-- @@ L21-28 verbatim
lemma numeratorExtension_periodic (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:O)}*Ideal.span {r})
      (numeratorExtension u a b r hr) := by
  intro x y hxy
  change numeratorBadTwist u a b r hr x*movingNumeratorRow r hr x=
    numeratorBadTwist u a b r hr y*movingNumeratorRow r hr y
  rw [numeratorBadTwist_periodic _ _ _ _ _ x y (Ideal.mul_le_left hxy),
    movingNumeratorRow_periodic _ _ x y (Ideal.mul_le_right hxy)]


-- @@ L30-36 verbatim
lemma numeratorExtension_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm


-- @@ L38-45 verbatim
lemma numeratorExtension_neg_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp only [Units.val_neg,hk]
  ring


-- @@ L47-54 verbatim
lemma numerator_good_norm_le (u : Oˣ) (a b : ℕ) (r k : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hk0))
  · apply map_dvd Ideal.absNorm
    rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨u.val*λ₀^a*(2:O)^b,by rw [hk];ring⟩


-- @@ L56-56 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end OAI
