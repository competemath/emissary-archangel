import OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteRankNormalized


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace SevenEighths.InverseMoment

-- @@ L8-8 verbatim
open ActualEisensteinCubic InverseTerminalWidths

-- @@ L9-9 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L11-20 verbatim
theorem actual_rank_parent_puncture (m:O)(hm:m≠0)(Z:ℝ)(hZ:1<Z):
    (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) :=by
  have hi:(Ideal.span {m}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm
  have hn:0<(Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ):=actual_ideal_norm_pos _ hi
  have hle:Ideal.absNorm (Ideal.span {m}:Ideal O).radical≤Ideal.absNorm (Ideal.span {m}:Ideal O):=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  unfold normWidth
  rw [Real.rpow_logb (by linarith:0<Z) (ne_of_gt hZ) hn]
  exact_mod_cast hle


-- @@ L22-22 verbatim
end SevenEighths.InverseMoment


-- @@ L24-24 verbatim
end


-- @@ L26-26 verbatim
end OAI
