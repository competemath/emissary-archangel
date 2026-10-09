import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.Clearing

-- @@ L8-8 verbatim
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]


-- @@ L10-25 verbatim
/-- Elements whose denominators can be cleared with a power of a fixed base element. -/
def subalgebra (f : S →ₐ[k] R) (p : S) : Subalgebra k R where
  carrier := {r | ∃ n : ℕ, ∃ s : S, f p ^ n * r = f s}
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨0,1,by simp⟩
  add_mem' := by
    rintro r s ⟨n,a,ha⟩ ⟨m,b,hb⟩
    refine ⟨n+m,p^m*a+p^n*b,?_⟩
    rw [map_add,map_mul,map_mul,map_pow,map_pow,← ha,← hb,pow_add]
    ring
  mul_mem' := by
    rintro r s ⟨n,a,ha⟩ ⟨m,b,hb⟩
    refine ⟨n+m,a*b,?_⟩
    rw [map_mul,← ha,← hb,pow_add]
    ring
  algebraMap_mem' c := ⟨0,algebraMap k S c,by simp⟩


-- @@ L27-27 verbatim
lemma mem_base (f : S →ₐ[k] R) (p s : S) : f s ∈ subalgebra f p := ⟨0,s,by simp⟩


-- @@ L29-42 verbatim
lemma injective_of_clearing {K : Type*} [CommRing K] [Algebra k K]
    (e : R →ₐ[k] K) (f : S →ₐ[k] R) (p : S)
    (hef : Function.Injective (e.comp f)) (hp : IsLeftRegular (f p))
    (h : subalgebra f p = ⊤) : Function.Injective e := by
  apply (injective_iff_map_eq_zero e).mpr
  intro r hr
  have hm : r ∈ subalgebra f p := by rw [h]; trivial
  obtain ⟨n,s,hs⟩ := hm
  have hz : s = 0 := by
    apply hef
    change e (f s) = e (f 0)
    rw [← hs,map_mul,hr,mul_zero,map_zero,map_zero]
  rw [hz,map_zero] at hs
  exact isLeftRegular_iff_right_eq_zero_of_mul.mp (hp.pow n) r hs


-- @@ L44-54 verbatim
lemma top_of_generators {ι : Type*} (q : MvPolynomial ι k →ₐ[k] R)
    (hq : Function.Surjective q) (f : S →ₐ[k] R) (p : S)
    (hX : ∀ i, q (MvPolynomial.X i) ∈ subalgebra f p) : subalgebra f p = ⊤ := by
  apply top_unique
  intro r hrTop
  clear hrTop
  obtain ⟨r,rfl⟩ := hq r
  induction r using MvPolynomial.induction_on with
  | C c => exact (q.commutes c) ▸ (subalgebra f p).algebraMap_mem c
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul]; exact mul_mem hr (hX i)


-- @@ L56-56 verbatim
end ComplexCancellation.Clearing


-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
