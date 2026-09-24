module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Arithmetic.BoundedCollection
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy


-- @@ L7-12 verbatim
/-!
# Prenex normal form for the arithmetical hierarchy

For `𝗜𝚺 s ⪯ T`, every `Hierarchy Γ s` formula `φ` is `T`-provably equivalent to `φ₀.toPrenex Γ s`
for some `φ₀ : ArithmeticSemisentence (n + s)` in `Hierarchy 𝚺 0`.
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open FFL


-- @@ L18-18 verbatim
namespace FFL.FirstOrder


-- @@ L20-20 verbatim
namespace Arithmetic


-- @@ L22-23 verbatim
structure Prenex (Γ : Polarity) (s : ℕ) (ξ : Type*) (n : ℕ) where
  matrix : 𝚺₀.Semiformula ξ (n + s)


-- @@ L25-25 verbatim
namespace Prenex


-- @@ L27-27 verbatim
variable {Γ : Polarity} {s : ℕ} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}

-- @@ L28-28 verbatim
variable {V : Type*} [ORingStructure V]


-- @@ L30-31 verbatim
@[coe]
def val (φ : Prenex Γ s ξ n) : ArithmeticSemiformula ξ n := φ.matrix.val.toPrenex Γ s


-- @@ L33-33 verbatim
instance : CoeTC (Prenex Γ s ξ n) (ArithmeticSemiformula ξ n) := ⟨val⟩


-- @@ L35-35 verbatim
def neg (φ : Prenex Γ s ξ n) : Prenex Γ.alt s ξ n := ⟨.mkSigma (∼φ.matrix.val) φ.matrix.sigma_prop.neg.of_zero⟩


-- @@ L37-37 verbatim
instance : HTilde (Prenex Γ s ξ n) (Prenex Γ.alt s ξ n) := ⟨neg⟩


-- @@ L39-39 verbatim
def rew (φ : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) : Prenex Γ s ξ₂ n₂ := ⟨φ.matrix.rew (ω.qpow s)⟩


-- @@ L41-41 verbatim
def sigma (φ : Prenex 𝚷 s ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩


-- @@ L43-43 verbatim
def pi (φ : Prenex 𝚺 s ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩


-- @@ L45-45 verbatim
def sigmaInv (φ : Prenex 𝚺 (s + 1) ξ n) : Prenex 𝚷 s ξ (n + 1) := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩


-- @@ L47-47 verbatim
def piInv (φ : Prenex 𝚷 (s + 1) ξ n) : Prenex 𝚺 s ξ (n + 1) := ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩


-- @@ L49-52 verbatim
def altUp (φ : Prenex Γ s ξ n) : Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _
  . exact (φ.rew Rew.bShift).pi
  . exact (φ.rew Rew.bShift).sigma


-- @@ L54-56 verbatim
def ofΔ₀ (φ : 𝚺₀.Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → Prenex Γ s ξ n
  | Γ, 0     => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)


-- @@ L58-58 verbatim
def verum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) Γ s


-- @@ L60-60 verbatim
def falsum : Prenex Γ s ξ n := ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) Γ s


-- @@ L62-63 verbatim
def rel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) Γ s


-- @@ L65-66 verbatim
def nrel (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ξ n) : Prenex Γ s ξ n :=
  ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) Γ s



-- @@ L69-72 verbatim
@[simp, grind .]
lemma val_hierarchy {φ : Prenex Γ s ξ n} : Hierarchy Γ s φ.val := by
  change Hierarchy Γ s (φ.matrix.val.toPrenex Γ s)
  simpa only [Nat.zero_add] using Hierarchy.toPrenex (Γ := Γ) (j := 0) φ.matrix.sigma_prop.of_zero


-- @@ L74-75 verbatim
@[simp, grind .]
lemma val_deltaZero {φ : Prenex Γ 0 ξ n} : Hierarchy 𝚺 0 φ.val := φ.matrix.sigma_prop


-- @@ L77-80 verbatim
@[simp, grind .]
lemma val_neg (φ : Prenex Γ s ξ n) : (∼φ).val = ∼φ.val := by
  show (neg φ).val = ∼φ.val
  simp [neg, val]


-- @@ L82-85 verbatim
@[simp, grind .]
lemma val_rew (φ : Prenex Γ s ξ₁ n₁) (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
  (φ.rew ω).val = ω ▹ φ.val := by
  simp [val, rew]


-- @@ L87-89 verbatim
@[simp, grind .]
lemma val_sigma {φ : Prenex 𝚷 s ξ (n + 1)} : φ.sigma.val = ∃¹ φ.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE]


-- @@ L91-93 verbatim
@[simp, grind .]
lemma val_pi {φ : Prenex 𝚺 s ξ (n + 1)} : φ.pi.val = ∀¹ φ.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE]


-- @@ L95-101 verbatim
@[simp, grind .]
lemma val_sigmaInv {φ : Prenex 𝚺 (s + 1) ξ n} : φ.val = ∃¹ φ.sigmaInv.val := by
  unfold val sigmaInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_sigma, ← Polarity.alt_sigma, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp




-- @@ L105-164 verbatim
@[simp, grind .]
lemma val_piInv {φ : Prenex 𝚷 (s + 1) ξ n} : φ.val = ∀¹ φ.piInv.val := by
  unfold val piInv
  simp only [HierarchySymbol.Semiformula.val_rew]
  rw [← Polarity.quant_pi, ← Polarity.alt_pi, ← Rewriting.quantItr_succ_smul_castLE,
    ← TransitiveRewriting.comp_app]
  simp

lemma models_sigmaInv (φ : Prenex 𝚺 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e φ.val ↔ ∃ x, V ⊧/(x :> e) φ.sigmaInv.val := by
  rw [val_sigmaInv]; exact Semiformula.eval_ex;

lemma models_piInv (φ : Prenex 𝚷 (s + 1) Empty n) (e : Fin n → V) :
    V ⊧/e φ.val ↔ ∀ x, V ⊧/(x :> e) φ.piInv.val := by
  rw [val_piInv]; exact Semiformula.eval_all;

lemma models_sigma (φ : Prenex 𝚷 s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e φ.sigma.val ↔ ∃ x, V ⊧/(x :> e) φ.val := by
  rw [val_sigma]; exact Semiformula.eval_ex;

lemma models_pi (φ : Prenex 𝚺 s Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e φ.pi.val ↔ ∀ x, V ⊧/(x :> e) φ.val := by
  rw [val_pi]; exact Semiformula.eval_all;

lemma models_altUp (φ : Prenex Γ s Empty n) (e : Fin n → V) :
  V ⊧/e φ.altUp.val ↔ V ⊧/e φ.val := by
  rcases Γ <;> simp [
    Polarity.eq_sigma, Polarity.alt_sigma, altUp,
    -val_piInv, -val_sigmaInv,
    Semiformula.eval_all, Nat.succ_eq_add_one
  ]

lemma models_ofΔ₀ (φ : 𝚺₀.Semisentence n) (e : Fin n → V) :
    V ⊧/e (ofΔ₀ φ Γ s).val ↔ V ⊧/e φ.val := by
  induction s generalizing Γ with
  | zero => rfl
  | succ s ih =>
    rcases Γ with _ | _
    . change V ⊧/e (ofΔ₀ φ 𝚷 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚷 s) e).trans (ih (Γ := 𝚷))
    . change V ⊧/e (ofΔ₀ φ 𝚺 s).altUp.val ↔ V ⊧/e φ.val
      exact (models_altUp (ofΔ₀ φ 𝚺 s) e).trans (ih (Γ := 𝚺))

lemma models_verum (e : Fin n → V) :
    V ⊧/e (verum : Prenex Γ s Empty n).val ↔ V ⊧/e (⊤ : ArithmeticSemisentence n) :=
  models_ofΔ₀ (.mkSigma ⊤ (Hierarchy.verum 𝚺 0 n)) e

lemma models_falsum (e : Fin n → V) :
    V ⊧/e (falsum : Prenex Γ s Empty n).val ↔ V ⊧/e (⊥ : ArithmeticSemisentence n) :=
  models_ofΔ₀ (.mkSigma ⊥ (Hierarchy.falsum 𝚺 0 n)) e

lemma models_rel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm Empty n)
    (e : Fin n → V) :
    V ⊧/e (rel r v : Prenex Γ s Empty n).val ↔ V ⊧/e (Semiformula.rel r v) :=
  models_ofΔ₀ (.mkSigma (.rel r v) (Hierarchy.rel 𝚺 0 r v)) e

lemma models_nrel {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm Empty n)
    (e : Fin n → V) :
    V ⊧/e (nrel r v : Prenex Γ s Empty n).val ↔ V ⊧/e (Semiformula.nrel r v) :=
  models_ofΔ₀ (.mkSigma (.nrel r v) (Hierarchy.nrel 𝚺 0 r v)) e


-- @@ L166-172 verbatim
variable {T : ArithmeticTheory}

lemma provable_iff_sigmaInv {φ' : Prenex 𝚺 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
  T ⊢ ∀¹* (φ 🡘 ∃¹ φ'.sigmaInv.val) := φ'.val_sigmaInv ▸ hφ'

lemma provable_iff_piInv {φ' : Prenex 𝚷 (s + 1) Empty n} (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) :
  T ⊢ ∀¹* (φ 🡘 ∀¹ φ'.piInv.val) := φ'.val_piInv ▸ hφ'


-- @@ L174-181 verbatim
mutual

def ball : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm ξ n → Prenex Γ s ξ (n + 1) → Prenex Γ s ξ n
  | _, 0    , _, u, φ => ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) φ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, φ => (ball (Rew.bShift u) (bexs ‘#1 + 1’ (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(bexs u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L183-188 verbatim
def bexs : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm ξ n → Prenex Γ s ξ (n + 1) → Prenex Γ s ξ n
  | _, 0    , _, u, φ => ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) φ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, u, φ => (bexs (Rew.bShift u) (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(ball u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L190-190 verbatim
end


-- @@ L192-192 verbatim
local notation:64 "∀'[" u "] " φ => Prenex.ball u φ

-- @@ L193-193 verbatim
local notation:64 "∃'[" u "] " φ => Prenex.bexs u φ


-- @@ L195-206 verbatim
@[simp]
lemma ball_zero {u : ArithmeticSemiterm ξ n} {φ : Prenex Γ 0 ξ (n + 1)} :
  (∀'[u] φ) = ⟨.mkSigma _ (Hierarchy.ball (Rew.bShift_positive u) φ.val_deltaZero)⟩ := by
  simp [ball]

lemma ball_succ_sigma {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚺 (s + 1) ξ (n + 1)} :
  (∀'[u] φ) = (∀'[Rew.bShift u] (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma := by
  rw [ball]

lemma ball_succ_pi {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚷 (s + 1) ξ (n + 1)} :
  (∀'[u] φ) = ∼(∃'[u] ∼φ) := by
  rw [ball]



-- @@ L209-220 verbatim
@[simp]
lemma bexs_zero {u : ArithmeticSemiterm ξ n} {φ : Prenex Γ 0 ξ (n + 1)} :
  (∃'[u] φ) = ⟨.mkSigma _ (Hierarchy.bexs (Rew.bShift_positive u) φ.val_deltaZero)⟩ := by
  simp [bexs]

lemma bexs_succ_sigma {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚺 (s + 1) ξ (n + 1)} :
  (∃'[u] φ) = (∃'[Rew.bShift u] (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma := by
  rw [bexs]

lemma bexs_succ_pi {u : ArithmeticSemiterm ξ n} {φ : Prenex 𝚷 (s + 1) ξ (n + 1)} :
  (∃'[u] φ) = ∼(∀'[u] ∼φ) := by
  rw [bexs]



-- @@ L223-231 verbatim
mutual

def and : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s ξ n → Prenex Γ s ξ n → Prenex Γ s ξ n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ =>
      (and (∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
           (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(or (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L233-237 verbatim
def or : {Γ : Polarity} → {s n : ℕ} → Prenex Γ s ξ n → Prenex Γ s ξ n → Prenex Γ s ξ n
  | _, 0    , _, φ, ψ => ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩
  | 𝚺, _ + 1, _, φ, ψ => (or φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(and (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L239-239 verbatim
end


-- @@ L241-241 verbatim
instance : HWedge (Prenex Γ s ξ n) (Prenex Γ s ξ n) (Prenex Γ s ξ n) := ⟨and⟩

-- @@ L242-242 verbatim
instance : HVee (Prenex Γ s ξ n) (Prenex Γ s ξ n) (Prenex Γ s ξ n) := ⟨or⟩


-- @@ L244-257 verbatim
@[simp]
lemma and_zero {φ ψ : Prenex Γ 0 ξ n} : (φ ⋏ ψ) = ⟨.mkSigma _ (Hierarchy.and φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  show and φ ψ = _
  simp [and]

lemma and_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) ξ n} :
  (φ ⋏ ψ) = ((∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))) ⋏
    (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma := by
  show and φ ψ = _
  rw [and]; rfl

lemma and_succ_pi {φ ψ : Prenex 𝚷 (s + 1) ξ n} : (φ ⋏ ψ) = ∼(∼φ ⋎ ∼ψ) := by
  show and φ ψ = _
  rw [and]; rfl



-- @@ L260-271 verbatim
@[simp]
lemma or_zero {φ ψ : Prenex Γ 0 ξ n} : (φ ⋎ ψ) = ⟨.mkSigma _ (Hierarchy.or φ.val_deltaZero ψ.val_deltaZero)⟩ := by
  show or φ ψ = _
  simp [or]

lemma or_succ_sigma {φ ψ : Prenex 𝚺 (s + 1) ξ n} : (φ ⋎ ψ) = (φ.sigmaInv ⋎ ψ.sigmaInv).sigma := by
  show or φ ψ = _
  rw [or]; rfl

lemma or_succ_pi {φ ψ : Prenex 𝚷 (s + 1) ξ n} : (φ ⋎ ψ) = ∼(∼φ ⋏ ∼ψ) := by
  show or φ ψ = _
  rw [or]; rfl


-- @@ L273-303 verbatim
private lemma models_bexs_witness [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (hb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
      (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val)
    (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (x w : V) (e : Fin n → V) :
    V ⊧/(x :> w :> e)
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val
      ↔ ∃ y ≤ w, V ⊧/(y :> x :> e) φ.sigmaInv.val := by
  rw [hb];
  have hswap : ∀ z : V,
      V ⊧/(z :> x :> w :> e) (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))).val ↔
        V ⊧/(z :> x :> e) φ.sigmaInv.val := by
    intro z;
    rw [val_rew, Semiformula.eval_rew];
    have hA : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) Empty.elim) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.bvar
        = (z :> x :> e : Fin (n + 2) → V) := by
      funext i;
      cases i using Fin.cases with
      | zero => simp;
      | succ i =>
        cases i using Fin.cases with
        | zero => simp;
        | succ i => simp;
    have hB : (Semiterm.val (L := ℒₒᵣ) (M := V) (z :> x :> w :> e) Empty.elim) ∘
        (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))) ∘ Semiterm.fvar
        = (Empty.elim : Empty → V) := by
      funext i; exact i.elim;
    rw [hA, hB];
  have hval : (‘#1 + 1’ : ArithmeticSemiterm Empty (n + 2)).valb (x :> w :> e) = w + 1 := by simp;
  rw [hval];
  simp only [hswap, Arithmetic.lt_succ_iff_le];


-- @@ L305-344 verbatim
mutual

theorem models_ball :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] → (u : ArithmeticSemiterm Empty n) →
      (φ : Prenex Γ s Empty (n + 1)) → (e : Fin n → V) →
    V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val
  | _, 0, _, _, u, φ, e => by
    simp [ball_zero, Prenex.val, Semiformula.eval_ball];
  | 𝚺, s + 1, _, _, u, φ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s + 1);
    have iha : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_ball u φ e;
    have ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs u φ e;
    rw [ball_succ_sigma (u := u) (φ := φ), models_sigma];
    simp only [iha (Rew.bShift u), Semiterm.val_bShift, models_bexs_witness ihb φ,
      models_sigmaInv φ];
    constructor;
    . rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;
    . intro h;
      have hθ : Hierarchy 𝚺 (s + 1) φ.sigmaInv.val := φ.sigmaInv.val_hierarchy.accum 𝚺;
      exact sigma_exists_bound_witness hθ e (u.valb e) h;
  | 𝚷, s + 1, _, _, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs u φ e;
    have hthis : V ⊧/e (∃'[u] ∼φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) (∼φ).val := ih u (∼φ) e;
    have hval : (∀'[u] φ).val = ∼(∃'[u] ∼φ).val := by
      rw [ball_succ_pi (u := u) (φ := φ)];
      exact val_neg (∃'[u] ∼φ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s n _inst _u _φ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L346-393 verbatim
theorem models_bexs :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] → (u : ArithmeticSemiterm Empty n) →
      (φ : Prenex Γ s Empty (n + 1)) → (e : Fin n → V) →
    V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val
  | _, 0, _, _, u, φ, e => by
    simp [bexs_zero, Prenex.val, Semiformula.eval_bexs];
  | 𝚺, s + 1, n, _, u, φ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚷 s Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∃'[u] φ).val ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_bexs u φ e;
    set φ₁' := φ.sigmaInv;
    set φ₁ := φ₁'.val;
    set v := #1 :> #0 :> fun i => #(i.succ.succ) with hv;
    let φ₂' := φ₁'.rew (Rew.subst v);
    have hswap : ∀ (x b : V), V ⊧/(x :> b :> e) φ₂'.val ↔ V ⊧/(b :> x :> e) φ₁ := by
      intro x b;
      rw [val_rew, Semiformula.eval_rew];
      have hA : (Semiterm.val (M := V) (x :> b :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.bvar
          = (b :> x :> e : Fin (n + 2) → V) := by
        funext i;
        cases i using Fin.cases with
        | zero => simp [hv];
        | succ i =>
          cases i using Fin.cases with
          | zero => simp [hv];
          | succ i => simp [hv];
      have hB : (Semiterm.val (M := V) (x :> b :> e) Empty.elim) ∘ (Rew.subst v) ∘ Semiterm.fvar
          = (Empty.elim : Empty → V) := by
        funext i; exact i.elim;
      rw [hA, hB];
    rw [bexs_succ_sigma (u := u) (φ := φ), val_sigma]
    show (∃ b, V ⊧/(b :> e) (∃'[Rew.bShift u] φ₂').val) ↔ ∃ x < u.valb e, V ⊧/(x :> e) φ.val;
    simp only [ih (Rew.bShift u) φ₂', Semiterm.val_bShift, hswap, models_sigmaInv φ];
    grind;
  | 𝚷, s + 1, _, _, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm Empty m) (φ : Prenex 𝚺 (s + 1) Empty (m + 1))
        (e : Fin m → V), V ⊧/e (∀'[u] φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) φ.val :=
      fun u φ e => models_ball u φ e;
    have hthis : V ⊧/e (∀'[u] ∼φ).val ↔ ∀ x < u.valb e, V ⊧/(x :> e) (∼φ).val := ih u (∼φ) e;
    have hval : (∃'[u] φ).val = ∼(∀'[u] ∼φ).val := by
      rw [bexs_succ_pi (u := u) (φ := φ)];
      exact val_neg (∀'[u] ∼φ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s n _inst _u _φ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L395-395 verbatim
end


-- @@ L397-444 verbatim
mutual

theorem models_and :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] → (φ ψ : Prenex Γ s Empty n) → (e : Fin n → V) →
    V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val
  | _, 0, _, _, φ, ψ, e => by
    simp [and_zero, Prenex.val];
  | 𝚺, s + 1, n, _, φ, ψ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s);
    have iha : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
      fun φ ψ e => models_and φ ψ e;
    rw [and_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
    set φ₂' := φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
    set ψ₂' := ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)));
    have hα_eval : ∀ z : V,
        V ⊧/(z :> e) (∃'[‘#0 + 1’] φ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) φ.sigmaInv.val := by
      intro z;
      rw [models_bexs ‘#0 + 1’ φ₂' (z :> e)];
      simp only [φ₂', val_rew, Semiformula.eval_insert1];
      simp [Arithmetic.lt_succ_iff_le];
    have hβ_eval : ∀ z : V,
        V ⊧/(z :> e) (∃'[‘#0 + 1’] ψ₂').val ↔ ∃ x ≤ z, V ⊧/(x :> e) ψ.sigmaInv.val := by
      intro z;
      rw [models_bexs ‘#0 + 1’ ψ₂' (z :> e)];
      simp only [ψ₂', val_rew, Semiformula.eval_insert1];
      simp [Arithmetic.lt_succ_iff_le];
    simp only [iha (∃'[‘#0 + 1’] φ₂') (∃'[‘#0 + 1’] ψ₂'), models_sigmaInv φ, models_sigmaInv ψ,
      hα_eval, hβ_eval];
    constructor;
    . rintro ⟨z, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
    . rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
  | 𝚷, s + 1, _, _, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
      fun φ ψ e => models_or φ ψ e;
    have hthis : V ⊧/e (∼φ ⋎ ∼ψ).val ↔ V ⊧/e (∼φ).val ∨ V ⊧/e (∼ψ).val := ih (∼φ) (∼ψ) e;
    have hval : (φ ⋏ ψ).val = ∼(∼φ ⋎ ∼ψ).val := by
      rw [and_succ_pi (φ := φ) (ψ := ψ)];
      exact val_neg (∼φ ⋎ ∼ψ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s n _inst _φ _ψ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L446-471 verbatim
theorem models_or :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] → (φ ψ : Prenex Γ s Empty n) → (e : Fin n → V) →
    V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val
  | _, 0, _, _, φ, ψ, e => by
    simp [or_zero, Prenex.val];
  | 𝚺, s + 1, _, _, φ, ψ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚷 s Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋎ ψ).val ↔ V ⊧/e φ.val ∨ V ⊧/e ψ.val :=
      fun φ ψ e => models_or φ ψ e;
    rw [or_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
    simp only [ih φ.sigmaInv ψ.sigmaInv, models_sigmaInv φ, models_sigmaInv ψ];
    exact exists_or;
  | 𝚷, s + 1, _, _, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : Prenex 𝚺 (s + 1) Empty m) (e : Fin m → V),
        V ⊧/e (φ ⋏ ψ).val ↔ V ⊧/e φ.val ∧ V ⊧/e ψ.val :=
      fun φ ψ e => models_and φ ψ e;
    have hthis : V ⊧/e (∼φ ⋏ ∼ψ).val ↔ V ⊧/e (∼φ).val ∧ V ⊧/e (∼ψ).val := ih (∼φ) (∼ψ) e;
    have hval : (φ ⋎ ψ).val = ∼(∼φ ⋏ ∼ψ).val := by
      rw [or_succ_pi (φ := φ) (ψ := ψ)];
      exact val_neg (∼φ ⋏ ∼ψ);
    rw [hval];
    simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      at hthis ⊢;
    grind;
termination_by Γ s n _inst _φ _ψ _e => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)


-- @@ L473-473 verbatim
end


-- @@ L475-476 verbatim
def exs (φ : Prenex 𝚺 (s + 1) ξ (n + 1)) : Prenex 𝚺 (s + 1) ξ n :=
  (∃'[‘#0 + 1’] (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma


-- @@ L478-478 verbatim
def all (φ : Prenex 𝚷 (s + 1) ξ (n + 1)) : Prenex 𝚷 (s + 1) ξ n := ∼(exs (∼φ))


-- @@ L480-480 verbatim
local prefix:64 "∃' " => Prenex.exs

-- @@ L481-524 verbatim
local prefix:64 "∀' " => Prenex.all

lemma models_exs [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ : Prenex 𝚺 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∃' φ).val ↔ ∃ x, V ⊧/(x :> e) φ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := s);
  show V ⊧/e
      (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
        (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma.val ↔
    ∃ x, V ⊧/(x :> e) φ.val;
  rw [models_sigma];
  have hβeval : ∀ z : V,
      V ⊧/(z :> e)
        (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
          (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).val ↔
        ∃ y ≤ z, V ⊧/(y :> z :> e)
          (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val := by
    intro z;
    rw [models_bexs];
    have hval : (‘#0 + 1’ : ArithmeticSemiterm Empty (n + 1)).valb (z :> e) = z + 1 := by simp;
    rw [hval];
    simp only [Arithmetic.lt_succ_iff_le];
  have hαeval : ∀ y z : V,
      V ⊧/(y :> z :> e)
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val ↔
        ∃ x ≤ z, V ⊧/(x :> y :> e) φ.sigmaInv.val :=
    fun y z => models_bexs_witness models_bexs φ y z e;
  simp only [hβeval, hαeval, models_sigmaInv φ];
  constructor;
  . rintro ⟨z, y, -, x, -, hx⟩;
    exact ⟨y, x, hx⟩;
  . rintro ⟨y, x, hx⟩;
    exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;

lemma models_all [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]
    (φ : Prenex 𝚷 (s + 1) Empty (n + 1)) (e : Fin n → V) :
    V ⊧/e (∀' φ).val ↔ ∀ x, V ⊧/(x :> e) φ.val := by
  have hthis : V ⊧/e (∃' ∼φ).val ↔ ∃ x, V ⊧/(x :> e) (∼φ).val := models_exs (∼φ) e;
  have hval : (∀' φ).val = ∼(∃' ∼φ).val := by
    unfold all;
    exact val_neg (∃' ∼φ);
  rw [hval];
  simp only [val_neg, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq] at hthis ⊢;
  grind;


-- @@ L526-623 verbatim
theorem models_exists_prenex {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ' : Prenex Γ s Empty n,
    ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] (e : Fin n → V), V ⊧/e φ ↔ V ⊧/e φ'.val := by
  induction h with
  | verum Γ s n =>
    use verum;
    intro V _ _ e;
    exact (models_verum e).symm;
  | falsum Γ s n =>
    use falsum;
    intro V _ _ e;
    exact (models_falsum e).symm;
  | rel Γ s r v =>
    use rel r v;
    intro V _ _ e;
    exact (models_rel r v e).symm;
  | nrel Γ s r v =>
    use nrel r v;
    intro V _ _ e;
    exact (models_nrel r v e).symm;
  | and _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋏ ψ';
    intro V _ _ e;
    rw [models_and φ' ψ' e];
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq];
    exact and_congr (hφ' V e) (hψ' V e);
  | or _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋎ ψ';
    intro V _ _ e;
    rw [models_or φ' ψ' e];
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq];
    exact or_congr (hφ' V e) (hψ' V e);
  | ball pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀'[u] φ';
    intro V _ _ e;
    rw [models_ball u φ' e];
    simp only [Semiformula.eval_ball];
    exact forall_congr' fun x => (imp_congr Iff.rfl (hφ' V (x :> e))).trans (by simp);
  | bexs pos _ ih =>
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃'[u] φ';
    intro V _ _ e;
    rw [models_bexs u φ' e];
    simp only [Semiformula.eval_bexs];
    exact exists_congr fun x => (and_congr Iff.rfl (hφ' V (x :> e))).trans (by simp);
  | @exs s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃' φ';
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_exs φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e);
  | @all s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀' φ';
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_all φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e);
  | @sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.sigma;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_sigma φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e);
  | @pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.pi;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (n₂ := s + 1) (by omega);
    rw [models_pi φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e);
  | @dummy_sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∀' φ').altUp;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (show s ≤ s + 1 + 1 by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := mod_ISigma_of_le (show s + 1 ≤ s + 1 + 1 by omega);
    exact Semiformula.eval_all.trans
      ((forall_congr' fun x => hφ' V (x :> e)).trans
        ((models_all φ' e).symm.trans (models_altUp (∀' φ') e).symm));
  | @dummy_pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∃' φ').altUp;
    intro V _ _ e;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := mod_ISigma_of_le (show s ≤ s + 1 + 1 by omega);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := mod_ISigma_of_le (show s + 1 ≤ s + 1 + 1 by omega);
    exact Semiformula.eval_ex.trans
      ((exists_congr fun x => hφ' V (x :> e)).trans
        ((models_exs φ' e).symm.trans (models_altUp (∃' φ') e).symm));


-- @@ L625-625 verbatim
end Prenex


-- @@ L627-636 verbatim
theorem exists_prenex_of_hierarchy {Γ : Polarity} {s : ℕ} (T : ArithmeticTheory) [𝗜𝚺 s ⪯ T]
  {n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ' : Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 φ'.val) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_ISigma (s := s);
  obtain ⟨φ', hφ'⟩ := Prenex.models_exists_prenex h;
  use φ';
  apply provable_iff_of_models_iff;
  intro V _ _ e;
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := models_of_subtheory (T := 𝗜𝚺 s) (U := T) (inferInstance);
  exact hφ' V e;


-- @@ L638-642 verbatim
theorem exists_matrix_provable {Γ : Polarity} {s: ℕ} (T : ArithmeticTheory) [𝗜𝚺 s ⪯ T]
  {n : ℕ} {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
  ∃ φ₀ : 𝚺₀.Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  obtain ⟨_, hφ'⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨_, by simpa [Prenex.val] using hφ'⟩;


-- @@ L644-644 verbatim
end Arithmetic


-- @@ L646-646 verbatim
end FFL.FirstOrder
