module

public import Foundation.FirstOrder.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-9 verbatim
/-!
# Formulas of monadic second-order logic
-/


-- @@ L11-11 verbatim
namespace FFL.SecondOrder


-- @@ L13-13 verbatim
open FirstOrder


-- @@ L15-29 verbatim
inductive Semiformula (L : Language) (Ξ ξ : Type*) : ℕ → ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L Ξ ξ N n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L Ξ ξ N n
  |   bvar : Fin N → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |  nbvar : Fin N → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |   fvar : Ξ → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |  nfvar : Ξ → Semiterm L ξ n → Semiformula L Ξ ξ N n
  |  verum : Semiformula L Ξ ξ N n
  | falsum : Semiformula L Ξ ξ N n
  |    and : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n
  |     or : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n
  |   all₁ : Semiformula L Ξ ξ N (n + 1) → Semiformula L Ξ ξ N n
  |   exs₁ : Semiformula L Ξ ξ N (n + 1) → Semiformula L Ξ ξ N n
  |   all₂ : Semiformula L Ξ ξ (N + 1) n → Semiformula L Ξ ξ N n
  |   exs₂ : Semiformula L Ξ ξ (N + 1) n → Semiformula L Ξ ξ N n


-- @@ L31-31 verbatim
abbrev Formula (L : Language) (Ξ ξ : Type*) := Semiformula L Ξ ξ 0 0


-- @@ L33-33 verbatim
abbrev Semisentence (L : Language) (n N : ℕ) := Semiformula L Empty Empty n N


-- @@ L35-35 verbatim
abbrev Sentence (L : Language) := Semiformula L Empty Empty 0 0


-- @@ L37-37 verbatim
abbrev Semiproposition (L : Language) (n N : ℕ) := Semiformula L ℕ ℕ n N


-- @@ L39-39 verbatim
abbrev Proposition (L : Language) := Semiformula L ℕ ℕ 0 0


-- @@ L41-41 verbatim
namespace Semiformula


-- @@ L43-43 verbatim
variable {L : Language} {Ξ ξ : Type*}


-- @@ L45-45 verbatim
instance : Top (Semiformula L Ξ ξ N n) := ⟨verum⟩


-- @@ L47-47 verbatim
instance : Bot (Semiformula L Ξ ξ N n) := ⟨falsum⟩


-- @@ L49-51 verbatim
instance : LogicalNeutral (Semiformula L Ξ ξ N n) where
  top := verum
  bot := falsum


-- @@ L53-53 verbatim
instance : Wedge (Semiformula L Ξ ξ N n) := ⟨and⟩


-- @@ L55-55 verbatim
instance : Vee (Semiformula L Ξ ξ N n) := ⟨or⟩


-- @@ L57-59 verbatim
instance : FirstOrder.Quantifier (Semiformula L Ξ ξ N) where
  all := all₁
  exs := exs₁


-- @@ L61-63 verbatim
instance : SecondOrder.Quantifier (Semiformula L Ξ ξ) where
  all₁ := all₂
  exs₁ := exs₂


-- @@ L65-65 verbatim
scoped notation:80 t " ∈# " X => Semiformula.bvar X t

-- @@ L66-66 verbatim
scoped notation:80 t " ∉# " X => Semiformula.nbvar X t

-- @@ L67-67 verbatim
scoped notation:80 t " ∈& " X => Semiformula.fvar X t

-- @@ L68-68 verbatim
scoped notation:80 t " ∉& " X => Semiformula.nfvar X t


-- @@ L70-84 verbatim
def neg : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ N n
  |  rel R v => nrel R v
  | nrel R v => rel R v
  |   t ∈# X => t ∉# X
  |   t ∉# X => t ∈# X
  |   t ∈& X => t ∉& X
  |   t ∉& X => t ∈& X
  |        ⊤ => ⊥
  |        ⊥ => ⊤
  |    φ ⋏ ψ => φ.neg ⋎ ψ.neg
  |    φ ⋎ ψ => φ.neg ⋏ ψ.neg
  |     ∀¹ φ => ∃¹ φ.neg
  |     ∃¹ φ => ∀¹ φ.neg
  |     ∀² φ => ∃² φ.neg
  |     ∃² φ => ∀² φ.neg


-- @@ L86-86 verbatim
instance : Tilde (Semiformula L Ξ ξ N n) := ⟨neg⟩


-- @@ L88-89 verbatim
instance : LogicalConnective (Semiformula L Ξ ξ N n) where
  arrow φ ψ := ∼φ ⋎ ψ


-- @@ L91-94 verbatim
instance : LogicalConnective.DeMorgan (Semiformula L Ξ ξ N n) where
  imply _ _ := rfl
  and _ _ := rfl
  or _ _ := rfl


-- @@ L96-98 verbatim
instance : LogicalNeutral.DeMorgan (Semiformula L Ξ ξ N n) where
  verum := rfl
  falsum := rfl


-- @@ L100-101 verbatim
@[simp] lemma neg_rel (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ∼(rel R v : Semiformula L Ξ ξ N n) = nrel R v := rfl


-- @@ L103-104 verbatim
@[simp] lemma neg_nrel (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ∼(nrel R v : Semiformula L Ξ ξ N n) = rel R v := rfl


-- @@ L106-107 verbatim
@[simp] lemma neg_bvar (X : Fin N) (t : Semiterm L ξ n) :
    ∼(t ∈# X : Semiformula L Ξ ξ N n) = t ∉# X := rfl


-- @@ L109-110 verbatim
@[simp] lemma neg_nbvar (X : Fin N) (t : Semiterm L ξ n) :
    ∼(t ∉# X : Semiformula L Ξ ξ N n) = t ∈# X := rfl


-- @@ L112-113 verbatim
@[simp] lemma neg_fvar (X : Ξ) (t : Semiterm L ξ n) :
    ∼(t ∈& X : Semiformula L Ξ ξ N n) = t ∉& X := rfl


-- @@ L115-116 verbatim
@[simp] lemma neg_nfvar (X : Ξ) (t : Semiterm L ξ n) :
    ∼(t ∉& X : Semiformula L Ξ ξ N n) = t ∈& X := rfl


-- @@ L118-119 verbatim
@[simp] lemma neg_all₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    ∼(∀¹ φ : Semiformula L Ξ ξ N n) = ∃¹ ∼φ := rfl


-- @@ L121-122 verbatim
@[simp] lemma neg_exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    ∼(∃¹ φ : Semiformula L Ξ ξ N n) = ∀¹ ∼φ := rfl


-- @@ L124-125 verbatim
@[simp] lemma neg_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ∼(∀² φ : Semiformula L Ξ ξ N n) = ∃² ∼φ := rfl


-- @@ L127-145 verbatim
@[simp] lemma neg_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    ∼(∃² φ : Semiformula L Ξ ξ N n) = ∀² ∼φ := rfl

lemma neg_neg (φ : Semiformula L Ξ ξ N n) : ∼∼φ = φ :=
  match φ with
  |  rel R v => rfl
  | nrel R v => rfl
  |   t ∈# X => rfl
  |   t ∉# X => rfl
  |   t ∈& X => rfl
  |   t ∉& X => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ => by simp [neg_neg φ, neg_neg ψ]
  |    φ ⋎ ψ => by simp [neg_neg φ, neg_neg ψ]
  |     ∀¹ φ => by simp [neg_neg φ]
  |     ∃¹ φ => by simp [neg_neg φ]
  |     ∀² φ => by simp [neg_neg φ]
  |     ∃² φ => by simp [neg_neg φ]


-- @@ L147-147 verbatim
instance : TildeInvolutive (Semiformula L Ξ ξ N n) := ⟨neg_neg⟩


-- @@ L149-150 verbatim
@[simp] lemma and_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L Ξ ξ N n} :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := iff_of_eq (by apply and.injEq)


-- @@ L152-153 verbatim
@[simp] lemma or_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L Ξ ξ N n} :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := iff_of_eq (by apply or.injEq)


-- @@ L155-156 verbatim
@[simp] lemma all₁_inj {φ ψ : Semiformula L Ξ ξ N (n + 1)} :
    ∀¹ φ = ∀¹ ψ ↔ φ = ψ := iff_of_eq (by apply all₁.injEq)


-- @@ L158-159 verbatim
@[simp] lemma exs₁_inj {φ ψ : Semiformula L Ξ ξ N (n + 1)} :
    ∃¹ φ = ∃¹ ψ ↔ φ = ψ := iff_of_eq (by apply exs₁.injEq)


-- @@ L161-162 verbatim
@[simp] lemma all₂_inj {φ ψ : Semiformula L Ξ ξ (N + 1) n} :
    ∀² φ = ∀² ψ ↔ φ = ψ := iff_of_eq (by apply all₂.injEq)


-- @@ L164-165 verbatim
@[simp] lemma exs₂_inj {φ ψ : Semiformula L Ξ ξ (N + 1) n} :
    ∃² φ = ∃² ψ ↔ φ = ψ := iff_of_eq (by apply exs₂.injEq)


-- @@ L167-197 verbatim
@[elab_as_elim]
def cases' {C : ∀ N n, Semiformula L Ξ ξ N n → Sort w}
    (hRel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (rel r v))
    (hNrel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (nrel r v))
    (hBvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∈# X))
    (hNbvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∉# X))
    (hFvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∈& X))
    (hNfvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∉& X))
    (hVerum : ∀ {N n}, C N n ⊤)
    (hFalsum : ∀ {N n}, C N n ⊥)
    (hAnd : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n (φ ⋏ ψ))
    (hOr : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n (φ ⋎ ψ))
    (hAll₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N n (∀¹ φ))
    (hExs₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N n (∃¹ φ))
    (hAll₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C N n (∀² φ))
    (hExs₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C N n (∃² φ))
    {N n} : (φ : Semiformula L Ξ ξ N n) → C N n φ
  |  rel r v => hRel r v
  | nrel r v => hNrel r v
  |   t ∈# X => hBvar X t
  |   t ∉# X => hNbvar X t
  |   t ∈& X => hFvar X t
  |   t ∉& X => hNfvar X t
  |        ⊤ => hVerum
  |        ⊥ => hFalsum
  |    φ ⋏ ψ => hAnd φ ψ
  |    φ ⋎ ψ => hOr φ ψ
  |     ∀¹ φ => hAll₁ φ
  |     ∃¹ φ => hExs₁ φ
  |     ∀² φ => hAll₂ φ
  |     ∃² φ => hExs₂ φ


-- @@ L199-233 verbatim
@[elab_as_elim]
def rec' {C : ∀ N n, Semiformula L Ξ ξ N n → Sort w}
    (hRel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (rel r v))
    (hNrel : ∀ {N n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C N n (nrel r v))
    (hBvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∈# X))
    (hNbvar : ∀ {N n} (X : Fin N) (t : Semiterm L ξ n), C N n (t ∉# X))
    (hFvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∈& X))
    (hNfvar : ∀ {N n} (X : Ξ) (t : Semiterm L ξ n), C N n (t ∉& X))
    (hVerum : ∀ {N n}, C N n ⊤)
    (hFalsum : ∀ {N n}, C N n ⊥)
    (hAnd : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n φ → C N n ψ → C N n (φ ⋏ ψ))
    (hOr : ∀ {N n} (φ ψ : Semiformula L Ξ ξ N n), C N n φ → C N n ψ → C N n (φ ⋎ ψ))
    (hAll₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N (n + 1) φ → C N n (∀¹ φ))
    (hExs₁ : ∀ {N n} (φ : Semiformula L Ξ ξ N (n + 1)), C N (n + 1) φ → C N n (∃¹ φ))
    (hAll₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C (N + 1) n φ → C N n (∀² φ))
    (hExs₂ : ∀ {N n} (φ : Semiformula L Ξ ξ (N + 1) n), C (N + 1) n φ → C N n (∃² φ))
    {N n} : (φ : Semiformula L Ξ ξ N n) → C N n φ
  |  rel r v => hRel r v
  | nrel r v => hNrel r v
  |   t ∈# X => hBvar X t
  |   t ∉# X => hNbvar X t
  |   t ∈& X => hFvar X t
  |   t ∉& X => hNfvar X t
  |        ⊤ => hVerum
  |        ⊥ => hFalsum
  |    φ ⋏ ψ => hAnd φ ψ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ ψ)
  |    φ ⋎ ψ => hOr φ ψ
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
    (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ ψ)
  |     ∀¹ φ => hAll₁ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
  |     ∃¹ φ => hExs₁ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
  |     ∀² φ => hAll₂ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)
  |     ∃² φ => hExs₂ φ (rec' hRel hNrel hBvar hNbvar hFvar hNfvar hVerum hFalsum hAnd hOr hAll₁ hExs₁ hAll₂ hExs₂ φ)


-- @@ L235-249 verbatim
def complexity : Semiformula L Ξ ξ N n → ℕ
  |  rel _ _ => 0
  | nrel _ _ => 0
  |   _ ∈# _ => 0
  |   _ ∉# _ => 0
  |   _ ∈& _ => 0
  |   _ ∉& _ => 0
  |        ⊤ => 0
  |        ⊥ => 0
  |    φ ⋏ ψ => max φ.complexity ψ.complexity + 1
  |    φ ⋎ ψ => max φ.complexity ψ.complexity + 1
  |     ∀¹ φ => φ.complexity + 1
  |     ∃¹ φ => φ.complexity + 1
  |     ∀² φ => φ.complexity + 1
  |     ∃² φ => φ.complexity + 1


-- @@ L251-252 verbatim
@[simp] lemma complexity_rel {k} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel R v : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L254-255 verbatim
@[simp] lemma complexity_nrel {k} (R : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel R v : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L257-258 verbatim
@[simp] lemma complexity_bvar (X : Fin N) (t : Semiterm L ξ n) :
    (t ∈# X : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L260-261 verbatim
@[simp] lemma complexity_nbvar (X : Fin N) (t : Semiterm L ξ n) :
    (t ∉# X : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L263-264 verbatim
@[simp] lemma complexity_fvar (X : Ξ) (t : Semiterm L ξ n) :
    (t ∈& X : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L266-267 verbatim
@[simp] lemma complexity_nfvar (X : Ξ) (t : Semiterm L ξ n) :
    (t ∉& X : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L269-269 verbatim
@[simp] lemma complexity_verum : (⊤ : Semiformula L Ξ ξ N n).complexity = 0 := rfl

-- @@ L270-270 verbatim
@[simp] lemma complexity_verum' : (verum : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L272-272 verbatim
@[simp] lemma complexity_falsum : (⊥ : Semiformula L Ξ ξ N n).complexity = 0 := rfl

-- @@ L273-273 verbatim
@[simp] lemma complexity_falsum' : (falsum : Semiformula L Ξ ξ N n).complexity = 0 := rfl


-- @@ L275-276 verbatim
@[simp] lemma complexity_and (φ ψ : Semiformula L Ξ ξ N n) :
    (φ ⋏ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L277-278 verbatim
@[simp] lemma complexity_and' (φ ψ : Semiformula L Ξ ξ N n) :
    (φ.and ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L280-281 verbatim
@[simp] lemma complexity_or (φ ψ : Semiformula L Ξ ξ N n) :
    (φ ⋎ ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L282-283 verbatim
@[simp] lemma complexity_or' (φ ψ : Semiformula L Ξ ξ N n) :
    (φ.or ψ).complexity = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L285-286 verbatim
@[simp] lemma complexity_all₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∀¹ φ).complexity = φ.complexity + 1 := rfl

-- @@ L287-288 verbatim
@[simp] lemma complexity_all₁' (φ : Semiformula L Ξ ξ N (n + 1)) :
    φ.all₁.complexity = φ.complexity + 1 := rfl


-- @@ L290-291 verbatim
@[simp] lemma complexity_exs₁ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∃¹ φ).complexity = φ.complexity + 1 := rfl

-- @@ L292-293 verbatim
@[simp] lemma complexity_exs₁' (φ : Semiformula L Ξ ξ N (n + 1)) :
    φ.exs₁.complexity = φ.complexity + 1 := rfl


-- @@ L295-296 verbatim
@[simp] lemma complexity_all₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∀² φ).complexity = φ.complexity + 1 := rfl

-- @@ L297-298 verbatim
@[simp] lemma complexity_all₂' (φ : Semiformula L Ξ ξ (N + 1) n) :
    φ.all₂.complexity = φ.complexity + 1 := rfl


-- @@ L300-301 verbatim
@[simp] lemma complexity_exs₂ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∃² φ).complexity = φ.complexity + 1 := rfl

-- @@ L302-303 verbatim
@[simp] lemma complexity_exs₂' (φ : Semiformula L Ξ ξ (N + 1) n) :
    φ.exs₂.complexity = φ.complexity + 1 := rfl


-- @@ L305-305 verbatim
end Semiformula


-- @@ L307-307 verbatim
end SecondOrder


-- @@ L309-309 verbatim
end FFL
