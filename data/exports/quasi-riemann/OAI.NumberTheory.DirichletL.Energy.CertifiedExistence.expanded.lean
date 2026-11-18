import OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor
import OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyCertifiedExistence

-- @@ L10-10 verbatim
open HeckeFamily CenteredMomentEnergyCappedWidthInduction

-- @@ L11-11 verbatim
open CenteredMomentEnergyCappedAnalyticSuccessor CenteredMomentEnergyCappedRadialTransport

-- @@ L12-12 verbatim
open CenteredMomentEnergyWidthSchedule

-- @@ L13-13 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L14-14 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L15-15 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L16-16 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L17-17 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L19-38 verbatim
theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∀k:ℕ,k≤count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k<count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious


-- @@ L40-48 verbatim
theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(_hrad:0<radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε hbeta hκ _ le_rfl


-- @@ L50-50 verbatim
end SevenEighths.CenteredMomentEnergyCertifiedExistence


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
