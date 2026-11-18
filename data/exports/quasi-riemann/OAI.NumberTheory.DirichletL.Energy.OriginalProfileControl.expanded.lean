import OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import OAI.NumberTheory.DirichletL.Energy.ZeroComparison
import OAI.NumberTheory.DirichletL.Moments.FirstReferenceEnergy
import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl

-- @@ L12-12 verbatim
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional

-- @@ L13-13 verbatim
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy

-- @@ L14-14 verbatim
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches

-- @@ L15-15 verbatim
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource

-- @@ L16-16 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]


-- @@ L18-24 verbatim
omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod₀ (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C^(Fintype.card ι):=by simp
    _≤C^N:=pow_le_pow_right₀ hC hN


-- @@ L26-37 verbatim
omit [DecidableEq ι] in
lemma plain_control_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    plainControl s (p.profile 0) (p.profile 1)≤C^N*p.control (insert (0,0) S) := by
  have h0 (i:Fin 2):SchwartzMap.seminorm ℝ 0 0 (p.profile i)≤
      sourceControl (insert (0,0) S) (p.profile i):=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
      (s:=insert (0,0) S) (i:=(0,0)) (x:=p.profile i) (Finset.mem_insert_self _ _)
  have hpair:=mul_le_mul (h0 0) (h0 1) (apply_nonneg _ _) (sourceControl_nonneg _ _)
  have hh:=mul_le_mul (slot_product_le s N C hC hN hM) hpair
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (pow_nonneg (by linarith) _)
  simpa only [plainControl,Profiles.control,mul_assoc] using hh


-- @@ L39-44 verbatim
omit [DecidableEq ι] in
lemma plain_control_sq_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    (plainControl s (p.profile 0) (p.profile 1))^2≤C^(2*N)*(p.control (insert (0,0) S))^2 := by
  have hh:=pow_le_pow_left₀ (plainControl_nonneg _ _ _) (plain_control_le s p S N C hC hN hM) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm N 2] using hh


-- @@ L46-48 verbatim
omit [DecidableEq ι] in
lemma zero_plain_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl


-- @@ L50-58 verbatim
omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod₀ (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))


-- @@ L60-75 verbatim
omit [DecidableEq ι] in
lemma source_factor_le (s:Input ι)(N:ℕ)(aslot a K:ℝ)(hs:0<aslot)(ha:0<a)(hK:0<K)
    (hN:Fintype.card ι≤N)(hlo:∀i,aslot≤s.lo i):
    sourceFactor s a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*(s.η.modulus.absNorm:ℝ) := by
  have hd:0<(min 1 aslot)^N*a*a:=by positivity
  have hprod:=lower_product s N aslot hs hN hlo
  have hden:(min 1 aslot)^N*a*a≤(∏i,s.lo i)*a*a:=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod ha.le) ha.le
  have hdiv:=div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hd hden
  have hc:=fixedPresentationCost_pos
  have hn:0≤(s.η.modulus.absNorm:ℝ):=Nat.cast_nonneg _
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdiv hc.le) hK.le) hn
  unfold sourceFactor
  convert hh using 1 ; ring


-- @@ L77-77 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L78-78 verbatim
section Input

-- @@ L79-79 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L80-80 verbatim
variable (Q : Ideal O) [NeZero Q]

-- @@ L81-81 verbatim
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)

-- @@ L82-82 verbatim
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)

-- @@ L83-83 verbatim
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)

-- @@ L84-84 verbatim
variable (W : ℝ → ℂ) (hW : Continuous W)

-- @@ L85-85 verbatim
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)

-- @@ L86-86 verbatim
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)

-- @@ L87-87 verbatim
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)

-- @@ L88-88 verbatim
variable {Z Bmask bΦ a b : ℝ}

-- @@ L89-89 verbatim
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)

-- @@ L90-90 verbatim
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)

-- @@ L91-91 verbatim
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)


-- @@ L93-94 verbatim
local notation "inp" => CenteredMomentEnergyNaturalInputMatches.input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame


-- @@ L96-101 verbatim
theorem natural_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ)):
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le inp p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)


-- @@ L103-109 verbatim
theorem natural_zero_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ))
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    (plainControl (zeroInput inp hz₁ hz₂) (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le (zeroInput inp hz₁ hz₂) p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)


-- @@ L111-115 verbatim
theorem natural_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K):
    sourceFactor inp a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le inp N aslot a K haslot ha hK hN (fun _=>le_refl _)


-- @@ L117-122 verbatim
theorem natural_zero_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K)
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    sourceFactor (zeroInput inp hz₁ hz₂) a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le (zeroInput inp hz₁ hz₂) N aslot a K haslot ha hK hN (fun _=>le_refl _)


-- @@ L124-124 verbatim
end Input

-- @@ L125-125 verbatim
end SevenEighths.CenteredMomentEnergyOriginalProfileControl


-- @@ L127-127 verbatim
end


-- @@ L129-129 verbatim
end OAI
