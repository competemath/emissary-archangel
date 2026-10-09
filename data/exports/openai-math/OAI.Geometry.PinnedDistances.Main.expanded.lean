import OAI.Geometry.PinnedDistances.ArithmeticSequence


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Filter

-- @@ L8-8 verbatim
open scoped Topology

-- @@ L9-9 verbatim
namespace WeakPinned


-- @@ L11-27 verbatim
/-- Uniform weak pinned planar distances for arbitrary real configurations. -/
theorem mainStatement : MainStatement := by
  classical
  by_contra hfail
  obtain ⟨c,s,γ,hc,hcγ,hγs,hs,hθ,P,C,hcard,hG,hmodels⟩ := sequence_arithmetic_model hfail
  choose L hL ii Z₁ Z₂ t hii h₁ h₂ ht0 ht using hmodels
  let K := fun j => L j
  let (j : ℕ) : NumberField (K j) := hL j
  have hn : Tendsto (fun j => (Fintype.card (C j):ℝ)) atTop atTop := by
    simpa only [Fintype.card_coe, Function.comp_def] using tendsto_natCast_atTop_atTop.comp (graph_card_tendsto hcard)
  apply arithmetic_sequence_impossible (fun j => coreGraph (P j) s (C j)) (Theta s) γ c
    (fun j => Theta s/((j:ℝ)+2)) Z₁ Z₂ h₁ h₂ hθ (hc.trans hcγ) (hγs.trans hs) hc hcγ hn
    (graph_error_tendsto (Theta s)) (fun j => by positivity) _ hG t ht
  intro j
  apply div_le_div_of_nonneg_left hθ.le (by norm_num : (0:ℝ)<2)
  have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith


-- @@ L29-30 verbatim
theorem main (s : ℝ) (hs : 0<s) : Tendsto (fun n : ℕ => F n s) atTop (𝓝 0) :=
  mainStatement s hs


-- @@ L32-32 verbatim
end WeakPinned


-- @@ L34-34 verbatim
end

-- @@ L35-35 verbatim
end


-- @@ L37-37 verbatim
end OAI
