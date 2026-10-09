import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.FactorDerivation

-- @@ L8-9 verbatim
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [IsDomain R]
  [Algebra k S] [Algebra k R]

-- @@ L10-12 verbatim
variable (f : S →ₐ[k] R) (hf : Function.Injective f)
  (D : Derivation k R R) (c : R) (hc : c ≠ 0)
  (h : ∀ s : S, ∃ t : S, D (f s)=c*f t)

-- @@ L13-13 verbatim
def value (s : S) : S := Classical.choose (h s)

-- @@ L14-15 verbatim
omit [IsDomain R] in
lemma specification (s : S) : D (f s)=c*f (value f D c h s) := Classical.choose_spec (h s)

-- @@ L16-20 verbatim
include hf hc in
lemma value_add (s t : S) : value f D c h (s+t)=value f D c h s+value f D c h t := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_add,map_add,map_add,mul_add,← specification,← specification]

-- @@ L21-25 verbatim
include hf hc in
lemma value_smul (a : k) (s : S) : value f D c h (a • s)=a • value f D c h s := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_smul,Derivation.map_smul,map_smul,mul_smul_comm,← specification]

-- @@ L26-33 verbatim
include hf hc in
lemma value_mul (s t : S) :
    value f D c h (s*t)=s*value f D c h t+t*value f D c h s := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul,
    specification f D c h s,specification f D c h t,map_add,map_mul,map_mul]
  ring

-- @@ L34-45 verbatim
def derivation : Derivation k S S where
  toLinearMap := {
    toFun := value f D c h
    map_add' := value_add f hf D c hc h
    map_smul' := value_smul f hf D c hc h }
  map_one_eq_zero' := by
    apply hf
    apply mul_left_cancel₀ hc
    change c*f (value f D c h 1)=c*f 0
    rw [← specification,map_one,Derivation.map_one_eq_zero,map_zero,mul_zero]
  leibniz' s t := by
    exact value_mul f hf D c hc h s t

-- @@ L46-46 verbatim
lemma apply_spec (s : S) : D (f s)=c*f (derivation f hf D c hc h s) := specification f D c h s

-- @@ L47-47 verbatim
end ComplexCancellation.FactorDerivation


-- @@ L49-49 verbatim
end


-- @@ L51-51 verbatim
end OAI
