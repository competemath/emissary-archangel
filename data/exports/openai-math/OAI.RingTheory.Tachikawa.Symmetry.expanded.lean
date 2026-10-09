import Mathlib


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
namespace Tachikawa


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
abbrev k := FractionRing (MvPolynomial (Fin 3) (ZMod 2))


-- @@ L12-15 verbatim
def SymmetricOver (K A : Type) [Field K] [Ring A] [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))


-- @@ L17-31 verbatim
def Counterexample : Prop :=
  ∃ (A : Type) (rA : Ring A),
    letI := rA
    ∃ (aA : Algebra k A),
      letI := aA
      Module.Finite k A ∧ SymmetricOver k A ∧
      ∃ (M : Type) (gM : AddCommGroup M),
        letI := gM
        ∃ (mA : Module A M) (mk : Module k M),
          letI := mA
          letI := mk
          IsScalarTower k A M ∧ Module.Finite k M ∧
          ¬ Module.Projective A M ∧
          ∀ n : ℕ, 0 < n →
            Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A M) n)


-- @@ L33-33 verbatim
end

-- @@ L34-34 verbatim
end Tachikawa




-- @@ L38-38 verbatim
noncomputable section

-- @@ L39-39 verbatim
namespace Tachikawa


-- @@ L41-41 verbatim
def DualBimodule (k R : Type*) [Field k] [Ring R] [Algebra k R] := Module.Dual k R


-- @@ L43-43 verbatim
namespace DualBimodule

-- @@ L44-44 verbatim
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]


-- @@ L46-46 verbatim
instance : FunLike (DualBimodule k R) R k := inferInstanceAs (FunLike (Module.Dual k R) R k)

-- @@ L47-48 verbatim
instance : LinearMapClass (DualBimodule k R) k R k :=
  inferInstanceAs (LinearMapClass (Module.Dual k R) k R k)


-- @@ L50-50 verbatim
instance : AddCommGroup (DualBimodule k R) := inferInstanceAs (AddCommGroup (Module.Dual k R))

-- @@ L51-51 verbatim
instance : Module k (DualBimodule k R) := inferInstanceAs (Module k (Module.Dual k R))


-- @@ L53-53 verbatim
@[ext] lemma ext {φ ψ : DualBimodule k R} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h


-- @@ L55-55 verbatim
@[simp] lemma add_apply (φ ψ : DualBimodule k R) (x : R) : (φ + ψ) x = φ x + ψ x := rfl

-- @@ L56-56 verbatim
@[simp] lemma zero_apply (x : R) : (0 : DualBimodule k R) x = 0 := rfl

-- @@ L57-57 verbatim
@[simp] lemma smul_apply (c : k) (φ : DualBimodule k R) (x : R) : (c • φ) x = c * φ x := rfl


-- @@ L59-66 verbatim
instance leftModule : Module R (DualBimodule k R) where
  smul a φ := φ.comp (LinearMap.mulRight k a)
  one_smul φ := by ext x; change φ (x * 1) = φ x; simp
  mul_smul a b φ := by ext x; change φ (x * (a * b)) = φ ((x * a) * b); simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by ext x; change φ (x * (a + b)) = φ (x * a) + φ (x * b); simp [mul_add]
  zero_smul φ := by ext x; change φ (x * 0) = 0; simp


-- @@ L68-68 verbatim
@[simp] lemma left_apply (a : R) (φ : DualBimodule k R) (x : R) : (a • φ) x = φ (x * a) := rfl


-- @@ L70-83 verbatim
instance rightModule : Module Rᵐᵒᵖ (DualBimodule k R) where
  smul a φ := φ.comp (LinearMap.mulLeft k a.unop)
  one_smul φ := by ext x; change φ (1 * x) = φ x; simp
  mul_smul a b φ := by
    ext x
    change φ ((b.unop * a.unop) * x) = φ (b.unop * (a.unop * x))
    simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by
    ext x
    change φ ((a.unop + b.unop) * x) = φ (a.unop * x) + φ (b.unop * x)
    simp [add_mul]
  zero_smul φ := by ext x; change φ (0 * x) = 0; simp


-- @@ L85-86 verbatim
@[simp] lemma right_apply (a : Rᵐᵒᵖ) (φ : DualBimodule k R) (x : R) :
    (a • φ) x = φ (a.unop * x) := rfl


-- @@ L88-89 verbatim
instance : SMulCommClass R Rᵐᵒᵖ (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp [mul_assoc]


-- @@ L91-94 verbatim
instance : IsScalarTower k R (DualBimodule k R) where
  smul_assoc a b φ := by
    ext x
    simp [Algebra.mul_smul_comm]


-- @@ L96-99 verbatim
instance : IsScalarTower k Rᵐᵒᵖ (DualBimodule k R) where
  smul_assoc a b φ := by
    ext x
    simp [Algebra.smul_mul_assoc]


-- @@ L101-102 verbatim
instance : SMulCommClass k R (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp


-- @@ L104-105 verbatim
instance : SMulCommClass k Rᵐᵒᵖ (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp


-- @@ L107-108 verbatim
instance [FiniteDimensional k R] : FiniteDimensional k (DualBimodule k R) :=
  inferInstanceAs (FiniteDimensional k (Module.Dual k R))


-- @@ L110-110 verbatim
end DualBimodule

-- @@ L111-111 verbatim
end Tachikawa




-- @@ L115-115 verbatim
namespace Tachikawa.DualBimodule

-- @@ L116-116 verbatim
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]


-- @@ L118-131 verbatim
def coinduce {Y : Type*} [AddCommGroup Y] [Module R Y] [Module k Y]
    [IsScalarTower k R Y] (g : Y →ₗ[k] k) : Y →ₗ[R] DualBimodule k R where
  toFun y :=
    { toFun := fun r => g (r • y)
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c r => by simp [smul_assoc] }
  map_add' a b := by
    ext r
    change g (r • (a + b)) = g (r • a) + g (r • b)
    simp [smul_add]
  map_smul' a y := by
    ext r
    change g (r • (a • y)) = g ((r * a) • y)
    rw [mul_smul]


-- @@ L133-135 verbatim
@[simp] lemma coinduce_apply {Y : Type*} [AddCommGroup Y] [Module R Y] [Module k Y]
    [IsScalarTower k R Y] (g : Y →ₗ[k] k) (y : Y) (r : R) :
    coinduce g y r = g (r • y) := rfl


-- @@ L137-161 verbatim
instance injective : Module.Injective R (DualBimodule k R) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let g₀ : X →ₗ[k] k :=
      { toFun := fun x => g x 1
        map_add' := fun x y => by simp
        map_smul' := fun c x => by
          change g (algebraMap k R c • x) 1 = c • g x 1
          rw [map_smul]
          simp [Algebra.algebraMap_eq_smul_one] }
    obtain ⟨s, hs⟩ := (f.restrictScalars k).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hf)
    refine ⟨coinduce (g₀.comp s), ?_⟩
    intro x
    ext r
    change g₀ (s (r • f x)) = g x r
    rw [← f.map_smul]
    have hs' : s (f (r • x)) = r • x := LinearMap.congr_fun hs (r • x)
    rw [hs']
    change g (r • x) 1 = g x r
    rw [map_smul]
    simp


-- @@ L163-163 verbatim
end Tachikawa.DualBimodule




-- @@ L167-167 verbatim
namespace Tachikawa


-- @@ L169-170 verbatim
abbrev TrivialExtension (k R : Type*) [Field k] [Ring R] [Algebra k R] :=
  TrivSqZeroExt R (DualBimodule k R)


-- @@ L172-172 verbatim
namespace TrivialExtension

-- @@ L173-173 verbatim
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]


-- @@ L175-176 verbatim
instance [FiniteDimensional k R] : FiniteDimensional k (TrivialExtension k R) :=
  inferInstanceAs (FiniteDimensional k (R × DualBimodule k R))


-- @@ L178-181 verbatim
def trace : TrivialExtension k R →ₗ[k] k where
  toFun a := a.snd 1
  map_add' a b := by simp
  map_smul' c a := by simp


-- @@ L183-183 verbatim
@[simp] lemma trace_apply (a : TrivialExtension k R) : trace a = a.snd 1 := rfl


-- @@ L185-188 verbatim
lemma trace_mul (a b : TrivialExtension k R) :
    trace (a * b) = b.snd a.fst + a.snd b.fst := by
  change (a.fst • b.snd + MulOpposite.op b.fst • a.snd) 1 = _
  simp


-- @@ L190-191 verbatim
lemma trace_comm (a b : TrivialExtension k R) : trace (a * b) = trace (b * a) := by
  rw [trace_mul, trace_mul, add_comm]


-- @@ L193-208 verbatim
lemma trace_nondegenerate (a : TrivialExtension k R)
    (h : ∀ b : TrivialExtension k R, trace (a * b) = 0) : a = 0 := by
  have hfst : a.fst = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff k a.fst).mp
    intro φ
    have := h (TrivSqZeroExt.inr (φ : DualBimodule k R))
    rw [trace_mul] at this
    change φ a.fst + a.snd 0 = 0 at this
    simpa using this
  have hsnd : a.snd = 0 := by
    ext r
    have := h (TrivSqZeroExt.inl r)
    rw [trace_mul] at this
    change (0 : DualBimodule k R) a.fst + a.snd r = 0 at this
    simpa using this
  exact TrivSqZeroExt.ext hfst hsnd


-- @@ L210-210 verbatim
end TrivialExtension




-- @@ L214-214 verbatim
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]


-- @@ L216-219 verbatim
structure SymmetrizingForm where
  linear : R →ₗ[k] k
  comm : ∀ a b, linear (a * b) = linear (b * a)
  nondegenerate : ∀ a, (∀ b, linear (a * b) = 0) → a = 0


-- @@ L221-221 verbatim
namespace SymmetrizingForm

-- @@ L222-222 verbatim
variable (t : SymmetrizingForm (k := k) (R := R))


-- @@ L224-224 verbatim
def toDual : R →ₗ[R] DualBimodule k R := DualBimodule.coinduce t.linear


-- @@ L226-226 verbatim
@[simp] lemma toDual_apply (a x : R) : t.toDual a x = t.linear (x * a) := rfl


-- @@ L228-235 verbatim
lemma toDual_injective : Function.Injective t.toDual := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  apply t.nondegenerate a
  intro b
  rw [t.comm]
  exact congrArg (fun f : DualBimodule k R => f b) ha


-- @@ L237-242 verbatim
def dualEquiv [FiniteDimensional k R] : R ≃ₗ[R] DualBimodule k R :=
  LinearEquiv.ofBijective t.toDual ⟨t.toDual_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show Module.finrank k R = Module.finrank k (DualBimodule k R) from
        (Subspace.dual_finrank_eq).symm) (f := t.toDual.restrictScalars k)).mp
          t.toDual_injective⟩


-- @@ L244-256 verbatim
include t in
lemma injective [FiniteDimensional k R] : Module.Injective R R := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R (DualBimodule k R) X Y f hf
    (t.dualEquiv.toLinearMap.comp g)
  refine ⟨t.dualEquiv.symm.toLinearMap.comp h, ?_⟩
  intro x
  change t.dualEquiv.symm (h (f x)) = g x
  have hhx := LinearMap.congr_fun hh x
  change h (f x) = t.dualEquiv (g x) at hhx
  rw [hhx]
  exact t.dualEquiv.symm_apply_apply (g x)


-- @@ L258-258 verbatim
end SymmetrizingForm


-- @@ L260-260 verbatim
namespace TrivialExtension


-- @@ L262-265 verbatim
def symmetrizingForm : SymmetrizingForm (k := k) (R := TrivialExtension k R) where
  linear := trace
  comm := trace_comm
  nondegenerate := trace_nondegenerate


-- @@ L267-268 verbatim
instance [FiniteDimensional k R] : Module.Injective (TrivialExtension k R) (TrivialExtension k R) :=
  symmetrizingForm.injective


-- @@ L270-270 verbatim
end TrivialExtension

-- @@ L271-271 verbatim
end Tachikawa




-- @@ L275-275 verbatim
namespace Tachikawa

-- @@ L276-276 verbatim
variable {K A : Type} [Field K] [Ring A] [Algebra K A]

-- @@ L277-288 verbatim
lemma SymmetrizingForm.symmetricOver (t : SymmetrizingForm (k := K) (R := A))
    [FiniteDimensional K A] : SymmetricOver K A := by
  refine ⟨t.dualEquiv.restrictScalars K, ?_, ?_⟩
  · intro a b c
    change t.linear (c * (a*b)) = t.linear ((c*a)*b)
    rw [mul_assoc]
  · intro a b c
    change t.linear (c * (a*b)) = t.linear ((b*c)*a)
    calc
      t.linear (c * (a*b)) = t.linear ((c*a)*b) := by rw [mul_assoc]
      _ = t.linear (b*(c*a)) := t.comm _ _
      _ = t.linear ((b*c)*a) := by rw [mul_assoc]

-- @@ L289-291 verbatim
lemma TrivialExtension.symmetricOver [FiniteDimensional K A] :
    SymmetricOver K (TrivialExtension K A) :=
  (TrivialExtension.symmetrizingForm (k := K) (R := A)).symmetricOver

-- @@ L292-292 verbatim
end Tachikawa




-- @@ L296-296 verbatim
namespace Tachikawa

-- @@ L297-307 verbatim
lemma counterexampleOf (A M : Type) [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite k A] [Module.Finite k M]
    (sym : SymmetricOver k A) (nonproj : ¬ Module.Projective A M)
    (van : ∀ n : ℕ, Subsingleton (CategoryTheory.Abelian.Ext
      (ModuleCat.of A M) (ModuleCat.of A M) (n+1))) : Counterexample := by
  refine ⟨A, inferInstance, inferInstance, inferInstance, sym, M, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, nonproj, ?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact van m

-- @@ L308-308 verbatim
end Tachikawa


-- @@ L310-310 verbatim
end


-- @@ L312-312 verbatim
end OAI
