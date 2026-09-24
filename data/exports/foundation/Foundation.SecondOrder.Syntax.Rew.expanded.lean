module

public import Foundation.SecondOrder.Syntax.Formula


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace Fin


-- @@ L9-9 verbatim
def retrusion (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) := 0 :> fun i ↦ (f i).succ


-- @@ L11-11 verbatim
@[simp] lemma retrusion_zero (f : Fin n → Fin m) : retrusion f 0 = 0 := rfl


-- @@ L13-14 verbatim
@[simp] lemma retrusion_succ (f : Fin n → Fin m) (i : Fin n) :
    retrusion f i.succ = (f i).succ := rfl


-- @@ L16-17 verbatim
@[simp] lemma retrusion_comp_succ (f : Fin n → Fin m) :
    retrusion f ∘ Fin.succ = Fin.succ ∘ f := by ext i; simp


-- @@ L19-20 verbatim
@[simp] lemma retrusion_id : retrusion (id : Fin n → Fin n) = id := by
  ext i; cases i using Fin.cases <;> simp


-- @@ L22-24 verbatim
@[simp] lemma retrusion_comp_retrusion (f : Fin n → Fin m) (g : Fin m → Fin p) :
    retrusion g ∘ retrusion f = retrusion (g ∘ f) := by
  ext i; cases i using Fin.cases <;> simp


-- @@ L26-26 verbatim
end Fin


-- @@ L28-28 verbatim
namespace FFL.SecondOrder


-- @@ L30-30 verbatim
open FirstOrder


-- @@ L32-32 verbatim
namespace Semiformula


-- @@ L34-34 verbatim
variable {L : Language} {Ξ ξ₁ ξ₂ : Type*}


-- @@ L36-54 verbatim
def rewAux (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L Ξ ξ₁ N n₁ → Semiformula L Ξ ξ₂ N n₂
  |  rel R v => rel R (ω ∘ v)
  | nrel R v => nrel R (ω ∘ v)
  |   t ∈# X => ω t ∈# X
  |   t ∉# X => ω t ∉# X
  |   t ∈& X => ω t ∈& X
  |   t ∉& X => ω t ∉& X
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => rewAux ω φ ⋏ rewAux ω ψ
  |    φ ⋎ ψ => rewAux ω φ ⋎ rewAux ω ψ
  |     ∀¹ φ => ∀¹ rewAux ω.q φ
  |     ∃¹ φ => ∃¹ rewAux ω.q φ
  |     ∀² φ => ∀² rewAux ω φ
  |     ∃² φ => ∃² rewAux ω φ

lemma rewAux_neg (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    rewAux ω (∼φ) = ∼rewAux ω φ := by
  induction φ using rec' generalizing n₂ <;> simp [rewAux, *]


-- @@ L56-63 verbatim
def rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L Ξ ξ₁ N n₁ →ˡᶜ Semiformula L Ξ ξ₂ N n₂ where
  toTr := rewAux ω
  map_top' := rfl
  map_bot' := rfl
  map_neg' φ := rewAux_neg _ _
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [LogicalConnective.DeMorgan.imply, rewAux, rewAux_neg]


-- @@ L65-77 verbatim
instance : Rewriting L ξ₁ (Semiformula L Ξ ξ₁ N) ξ₂ (Semiformula L Ξ ξ₂ N) where
  app := rew
  app_all (_ _) := rfl
  app_exs (_ _) := rfl

lemma rew_rel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ (rel r v : Semiformula L Ξ ξ₁ N n₁) = rel r fun i ↦ ω (v i) := rfl

lemma rew_rel_eq_comp (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ (rel r v : Semiformula L Ξ ξ₁ N n₁) = rel r (ω ∘ v) := rfl

lemma rew_nrel (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω ▹ (nrel r v : Semiformula L Ξ ξ₁ N n₁) = nrel r fun i ↦ ω (v i) := rfl


-- @@ L79-80 verbatim
@[simp] lemma rew_bvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Fin N) :
    ω ▹ (t ∈# X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∈# X := rfl


-- @@ L82-83 verbatim
@[simp] lemma rew_nbvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Fin N) :
    ω ▹ (t ∉# X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∉# X := rfl


-- @@ L85-86 verbatim
@[simp] lemma rew_fvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Ξ) :
    ω ▹ (t ∈& X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∈& X := rfl


-- @@ L88-89 verbatim
@[simp] lemma rew_nfvar (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) (X : Ξ) :
    ω ▹ (t ∉& X : Semiformula L Ξ ξ₁ N n₁) = (ω t) ∉& X := rfl


-- @@ L91-92 verbatim
@[simp] lemma rew_all₀ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ (∀¹ φ) = ∀¹ (ω.q ▹ φ) := rfl


-- @@ L94-95 verbatim
@[simp] lemma rew_exs₀ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N (n₁ + 1)) :
    ω ▹ (∃¹ φ) = ∃¹ (ω.q ▹ φ) := rfl


-- @@ L97-98 verbatim
@[simp] lemma rew_all₁ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ (N + 1) n₁) :
    ω ▹ (∀² φ) = ∀² (ω ▹ φ) := rfl


-- @@ L100-101 verbatim
@[simp] lemma rew_exs₁ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ (N + 1) n₁) :
    ω ▹ (∃² φ) = ∃² (ω ▹ φ) := rfl


-- @@ L103-104 verbatim
instance : ReflectiveRewriting L ξ (Semiformula L Ξ ξ N) where
  id_app (φ) := by induction φ using rec' <;> simp [rew_rel, rew_nrel, *]


-- @@ L106-108 verbatim
instance : TransitiveRewriting L ξ₁ (Semiformula L Ξ ξ₁ N) ξ₂ (Semiformula L Ξ ξ₂ N) ξ₃ (Semiformula L Ξ ξ₃ N) where
  comp_app {n₁ n₂ n₃ ω₁₂ ω₂₃ φ} := by
    induction φ using rec' generalizing n₂ n₃ <;> simp [rew_rel, rew_nrel, Rew.comp_app, Rew.q_comp, *]


-- @@ L110-128 verbatim
def bmapAux (f : Fin N → Fin M) : Semiformula L Ξ ξ N n → Semiformula L Ξ ξ M n
  |  rel R v => rel R v
  | nrel R v => nrel R v
  |   t ∈# X => t ∈# f X
  |   t ∉# X => t ∉# f X
  |   t ∈& X => t ∈& X
  |   t ∉& X => t ∉& X
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.bmapAux f ⋏ ψ.bmapAux f
  |    φ ⋎ ψ => φ.bmapAux f ⋎ ψ.bmapAux f
  |     ∀¹ φ => ∀¹ φ.bmapAux f
  |     ∃¹ φ => ∃¹ φ.bmapAux f
  |     ∀² φ => ∀² φ.bmapAux (Fin.retrusion f)
  |     ∃² φ => ∃² φ.bmapAux (Fin.retrusion f)

lemma bmapAux_neg {f : Fin N → Fin M} (φ : Semiformula L Ξ ξ N n) :
    (∼φ).bmapAux f = ∼(φ.bmapAux f) := by
  induction φ using rec' generalizing M <;> simp [bmapAux, *]


-- @@ L130-137 verbatim
def bmap (f : Fin N → Fin M) : Semiformula L Ξ ξ N n →ˡᶜ Semiformula L Ξ ξ M n where
  toTr := bmapAux f
  map_top' := rfl
  map_bot' := rfl
  map_neg' φ := bmapAux_neg _
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [LogicalConnective.DeMorgan.imply, bmapAux_neg, bmapAux]


-- @@ L139-139 verbatim
section bmap


-- @@ L141-141 verbatim
variable {f : Fin N → Fin M}


-- @@ L143-144 verbatim
@[simp] lemma bmap_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v : Semiformula L Ξ ξ N n).bmap f = rel r v := rfl


-- @@ L146-147 verbatim
@[simp] lemma bmap_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v : Semiformula L Ξ ξ N n).bmap f = nrel r v := rfl


-- @@ L149-150 verbatim
@[simp] lemma bmap_bvar (t : Semiterm L ξ n) (X : Fin N) :
    (t ∈# X : Semiformula L Ξ ξ N n).bmap f = t ∈# f X := rfl


-- @@ L152-153 verbatim
@[simp] lemma bmap_nbvar (t : Semiterm L ξ n) (X : Fin N) :
    (t ∉# X : Semiformula L Ξ ξ N n).bmap f = t ∉# f X := rfl


-- @@ L155-156 verbatim
@[simp] lemma bmap_fvar (t : Semiterm L ξ n) (X : Ξ) :
    (t ∈& X : Semiformula L Ξ ξ N n).bmap f = t ∈& X := rfl


-- @@ L158-159 verbatim
@[simp] lemma bmap_nfvar (t : Semiterm L ξ n) (X : Ξ) :
    (t ∉& X : Semiformula L Ξ ξ N n).bmap f = t ∉& X := rfl


-- @@ L161-162 verbatim
@[simp] lemma bmap_all₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∀¹ φ).bmap f = ∀¹ (φ.bmap f) := rfl


-- @@ L164-165 verbatim
@[simp] lemma bmap_exs₀ (φ : Semiformula L Ξ ξ N (n + 1)) :
    (∃¹ φ).bmap f = ∃¹ (φ.bmap f) := rfl


-- @@ L167-168 verbatim
@[simp] lemma bmap_all₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∀² φ).bmap f = ∀² (φ.bmap (Fin.retrusion f)) := rfl


-- @@ L170-175 verbatim
@[simp] lemma bmap_exs₁ (φ : Semiformula L Ξ ξ (N + 1) n) :
    (∃² φ).bmap f = ∃² (φ.bmap (Fin.retrusion f)) := rfl

lemma bmap_comp {M N n} (f : Fin N → Fin M) (g : Fin M → Fin P) (φ : Semiformula L Ξ ξ N n) :
    (φ.bmap f).bmap g = φ.bmap (g ∘ f) := by
  induction φ using Semiformula.rec' generalizing M P <;> simp [*]


-- @@ L177-185 verbatim
end bmap

lemma bmap_comm (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) (f : Fin N → Fin M) :
    (ω ▹ φ).bmap f = ω ▹ φ.bmap f := by
  match φ with
  | .rel R v | .nrel R v | t ∈# X | t ∉# X | t ∈& X | t ∉& X | ⊤ | ⊥ => rfl
  | φ ⋏ ψ | φ ⋎ ψ => simp [bmap_comm ω φ, bmap_comm ω ψ]
  | ∀¹ φ | ∃¹ φ => simp [bmap_comm ω.q φ]
  | ∀² φ | ∃² φ => simp [bmap_comm ω φ]


-- @@ L187-187 verbatim
end Semiformula


-- @@ L189-192 verbatim
@[ext]
structure Rew (L : Language) (Ξ₁ : Type*) (N₁ : ℕ) (Ξ₂ : Type*) (N₂ : ℕ) (ξ : Type*) where
  bv : Fin N₁ → Semiformula L Ξ₂ ξ N₂ 1
  fv : Ξ₁ → Semiformula L Ξ₂ ξ N₂ 1


-- @@ L194-194 verbatim
namespace Rew


-- @@ L196-196 verbatim
open Semiformula


-- @@ L198-198 verbatim
variable {L : Language} {Ξ₁ Ξ₂ ξ : Type*}


-- @@ L200-202 verbatim
def map (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₁) (ω : FirstOrder.Rew L ξ₁ 1 ξ₂ 1) : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₂ where
  bv X := ω ▹ Ω.bv X
  fv X := ω ▹ Ω.fv X


-- @@ L204-205 verbatim
@[simp] lemma map_bv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₁) (ω : FirstOrder.Rew L ξ₁ 1 ξ₂ 1) (X : Fin N₁) :
    (Ω.map ω).bv X = ω ▹ Ω.bv X := by rfl


-- @@ L207-208 verbatim
@[simp] lemma map_fv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ₁) (ω : FirstOrder.Rew L ξ₁ 1 ξ₂ 1) (X : Ξ₁) :
    (Ω.map ω).fv X = ω ▹ Ω.fv X := by rfl


-- @@ L210-212 verbatim
def q (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ (N₁ + 1) Ξ₂ (N₂ + 1) ξ where
  bv := (#0 ∈# 0) :> fun X ↦ (Ω.bv X).bmap Fin.succ
  fv X := (Ω.fv X).bmap Fin.succ


-- @@ L214-214 verbatim
local postfix:max "𐞥" => q


-- @@ L216-217 verbatim
@[simp] lemma q_bv_zero (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω𐞥.bv 0 = #0 ∈# 0 := by rfl


-- @@ L219-220 verbatim
@[simp] lemma q_bv_succ (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    Ω𐞥.bv X.succ = (Ω.bv X).bmap Fin.succ := by rfl


-- @@ L222-223 verbatim
@[simp] lemma q_fv (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    Ω𐞥.fv X = (Ω.fv X).bmap Fin.succ := by rfl


-- @@ L225-243 verbatim
def appAux (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Semiformula L Ξ₁ ξ N₁ n → Semiformula L Ξ₂ ξ N₂ n
  |  .rel R v => .rel R v
  | .nrel R v => .nrel R v
  |    t ∈# X => (Ω.bv X)/[t]
  |    t ∉# X => ∼(Ω.bv X)/[t]
  |    t ∈& X => (Ω.fv X)/[t]
  |    t ∉& X => ∼(Ω.fv X)/[t]
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ ψ => Ω.appAux φ ⋏ Ω.appAux ψ
  |     φ ⋎ ψ => Ω.appAux φ ⋎ Ω.appAux ψ
  |      ∀¹ φ => ∀¹ Ω.appAux φ
  |      ∃¹ φ => ∃¹ Ω.appAux φ
  |      ∀² φ => ∀² Ω𐞥.appAux φ
  |      ∃² φ => ∃² Ω𐞥.appAux φ

lemma appAux_neg (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    Ω.appAux (∼φ) = ∼Ω.appAux φ := by
  induction φ using Semiformula.rec' generalizing N₂ <;> simp [appAux, *]


-- @@ L245-252 verbatim
def app (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Semiformula L Ξ₁ ξ N₁ n →ˡᶜ Semiformula L Ξ₂ ξ N₂ n where
  toTr := Ω.appAux
  map_top' := rfl
  map_bot' := rfl
  map_neg' := by simp [appAux_neg]
  map_and' _ _ := rfl
  map_or' _ _ := rfl
  map_imply' _ _ := by simp [LogicalConnective.DeMorgan.imply, appAux_neg, appAux]


-- @@ L254-254 verbatim
local infix:73 " • " => app


-- @@ L256-256 verbatim
section


-- @@ L258-258 verbatim
variable (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ)


-- @@ L260-261 verbatim
@[simp] lemma app_rel (r : L.Rel k) (v) :
    Ω • (.rel r v : Semiformula L Ξ₁ ξ N₁ n) = .rel r v := rfl


-- @@ L263-264 verbatim
@[simp] lemma app_nrel (r : L.Rel k) (v) :
    Ω • (.nrel r v : Semiformula L Ξ₁ ξ N₁ n) = .nrel r v := rfl


-- @@ L266-267 verbatim
@[simp] lemma app_bvar (t : Semiterm L ξ n) (X : Fin N₁) :
    Ω • (t ∈# X : Semiformula L Ξ₁ ξ N₁ n) = (Ω.bv X)/[t] := rfl


-- @@ L269-270 verbatim
@[simp] lemma app_nbvar (t : Semiterm L ξ n) (X : Fin N₁) :
    Ω • (t ∉# X : Semiformula L Ξ₁ ξ N₁ n) = ∼(Ω.bv X)/[t] := rfl


-- @@ L272-273 verbatim
@[simp] lemma app_fvar (t : Semiterm L ξ n) (X : Ξ₁) :
    Ω • (t ∈& X : Semiformula L Ξ₁ ξ N₁ n) = (Ω.fv X)/[t] := rfl


-- @@ L275-276 verbatim
@[simp] lemma app_nfvar (t : Semiterm L ξ n) (X : Ξ₁) :
    Ω • (t ∉& X : Semiformula L Ξ₁ ξ N₁ n) = ∼(Ω.fv X)/[t] := rfl


-- @@ L278-279 verbatim
@[simp] lemma app_all₀ (φ : Semiformula L Ξ₁ ξ N₁ (n + 1)) :
    Ω • (∀¹ φ) = ∀¹ Ω • φ := rfl


-- @@ L281-282 verbatim
@[simp] lemma app_exs₀ (φ : Semiformula L Ξ₁ ξ N₁ (n + 1)) :
    Ω • (∃¹ φ) = ∃¹ Ω • φ := rfl


-- @@ L284-285 verbatim
@[simp] lemma app_all₁ (φ : Semiformula L Ξ₁ ξ (N₁ + 1) n) :
    Ω • (∀² φ) = ∀² Ω𐞥 • φ := rfl


-- @@ L287-288 verbatim
@[simp] lemma app_exs₁ (φ : Semiformula L Ξ₁ ξ (N₁ + 1) n) :
    Ω • (∃² φ) = ∃² Ω𐞥 • φ := rfl


-- @@ L290-296 verbatim
end

lemma app_comm_subst {N₁ N₂} (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (v : Fin n₁ → Semiterm L ξ n₂) (φ : Semiformula L Ξ₁ ξ N₁ n₁) :
    Ω • (FirstOrder.Rew.subst v ▹ φ) = FirstOrder.Rew.subst v ▹ (Ω • φ) := by
  induction φ using Semiformula.rec' generalizing N₂ n₂ <;>
    simp [*, ←FirstOrder.TransitiveRewriting.comp_app, FirstOrder.Rew.subst_comp_subst, FirstOrder.Rew.q_subst,
      Semiformula.rew_rel, Semiformula.rew_nrel]


-- @@ L298-300 verbatim
protected def id : Rew L Ξ N Ξ N ξ where
  bv X := #0 ∈# X
  fv X := #0 ∈& X


-- @@ L302-303 verbatim
@[simp] lemma id_bv (X : Fin N) :
    (Rew.id : Rew L Ξ N Ξ N ξ).bv X = #0 ∈# X := by rfl


-- @@ L305-306 verbatim
@[simp] lemma id_fv (X : Ξ) :
    (Rew.id : Rew L Ξ N Ξ N ξ).fv X = #0 ∈& X := by rfl


-- @@ L308-312 verbatim
@[simp] lemma q_id :
    (Rew.id : Rew L Ξ N Ξ N ξ)𐞥 = Rew.id := by
  ext X
  · cases X using Fin.cases <;> simp
  · simp


-- @@ L314-316 verbatim
@[simp] lemma app_id (φ : Semiformula L Ξ ξ N n) :
    Rew.id • φ = φ := by
  induction φ using Semiformula.rec' <;> simp [*]


-- @@ L318-320 verbatim
def comp (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ N₁ Ξ₃ N₃ ξ where
  bv X := Ω₂₃ • Ω₁₂.bv X
  fv X := Ω₂₃ • Ω₁₂.fv X


-- @@ L322-323 verbatim
@[simp] lemma comp_bv (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    (Ω₂₃.comp Ω₁₂).bv X = Ω₂₃ • Ω₁₂.bv X := rfl


-- @@ L325-326 verbatim
@[simp] lemma comp_fv (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    (Ω₂₃.comp Ω₁₂).fv X = Ω₂₃ • Ω₁₂.fv X := rfl


-- @@ L328-330 verbatim
def bLeft (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ N₁ Ξ₂ N₃ ξ where
  bv X := (Ω.bv X).bmap f
  fv X := (Ω.fv X).bmap f


-- @@ L332-333 verbatim
@[simp] lemma bLeft_bv (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₁) :
    (Ω.bLeft f).bv X = (Ω.bv X).bmap f := rfl


-- @@ L335-346 verbatim
@[simp] lemma bLeft_fv (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    (Ω.bLeft f).fv X = (Ω.fv X).bmap f := rfl

lemma bLeft_q (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (f : Fin N₂ → Fin N₃) :
    (Ω.bLeft f)𐞥 = Ω𐞥.bLeft (Fin.retrusion f) := by
  ext X
  · cases X using Fin.cases <;> simp [q_bv_succ, bLeft_bv, bmap_comp]
  · simp [q_fv, bLeft_fv, bmap_comp]

lemma app_bmap_eq_bLeft (f : Fin N₂ → Fin N₃) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    (Ω • φ).bmap f = Ω.bLeft f • φ := by
  induction φ using Semiformula.rec' generalizing N₂ N₃ <;> simp [*, bmap_comm, bLeft_q]


-- @@ L348-350 verbatim
def bRight (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) : Rew L Ξ₁ N₀ Ξ₂ N₂ ξ where
  bv X := Ω.bv (f X)
  fv X := Ω.fv X


-- @@ L352-353 verbatim
@[simp] lemma bRight_bv (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Fin N₀) :
    (Ω.bRight f).bv X = Ω.bv (f X) := rfl


-- @@ L355-366 verbatim
@[simp] lemma bRight_fv (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (X : Ξ₁) :
    (Ω.bRight f).fv X = Ω.fv X := rfl

lemma bRight_q (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    (Ω.bRight f)𐞥 = Ω𐞥.bRight (Fin.retrusion f) := by
  ext X
  · cases X using Fin.cases <;> simp [bRight_bv]
  · simp [bRight_fv]

lemma bmap_app_eq (f : Fin N₀ → Fin N₁) (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₀ n) :
    Ω • φ.bmap f = Ω.bRight f • φ := by
  induction φ using Semiformula.rec' generalizing N₁ N₂ <;> simp [*, bRight_q]


-- @@ L368-369 verbatim
@[simp] lemma q_bRight_succ (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω𐞥.bRight Fin.succ = Ω.bLeft Fin.succ := by rfl


-- @@ L371-379 verbatim
@[simp] lemma q_comp_eq (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    (Ω₂₃.comp Ω₁₂)𐞥 = Ω₂₃𐞥.comp Ω₁₂𐞥 := by
  ext X
  · cases X using Fin.cases <;> simp [comp, app_bmap_eq_bLeft, bmap_app_eq]
  · simp [comp, app_bmap_eq_bLeft, bmap_app_eq]

lemma app_comp (Ω₂₃ : Rew L Ξ₂ N₂ Ξ₃ N₃ ξ) (Ω₁₂ : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) (φ : Semiformula L Ξ₁ ξ N₁ n) :
    (Ω₂₃.comp Ω₁₂) • φ = Ω₂₃ • (Ω₁₂ • φ) := by
  induction φ using Semiformula.rec' generalizing N₂ N₃ <;> simp [*, app_comm_subst]


-- @@ L381-382 verbatim
@[simp] lemma one_comp (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Rew.id.comp Ω = Ω := by ext X <;> simp


-- @@ L384-385 verbatim
@[simp] lemma comp_one (Ω : Rew L Ξ₁ N₁ Ξ₂ N₂ ξ) :
    Ω.comp Rew.id = Ω := by ext X <;> simp


-- @@ L387-389 verbatim
def free : Rew L ℕ (N + 1) ℕ N ξ where
  bv := (#0 ∈# ·) <: #0 ∈& 0
  fv X := #0 ∈& (X + 1)


-- @@ L391-391 verbatim
section free


-- @@ L393-394 verbatim
@[simp] lemma free_bvar_castSucc_eq (X : Fin N) :
    (free (L := L) (ξ := ξ)).bv (Fin.castSucc X) = #0 ∈# X := by simp [free]


-- @@ L396-397 verbatim
@[simp] lemma free_bvar_last (N : ℕ) :
    (free (L := L) (ξ := ξ)).bv (Fin.last N) = #0 ∈& 0 := by simp [free]


-- @@ L399-400 verbatim
@[simp] lemma free_fvar (X : ℕ) :
    (free (L := L) (ξ := ξ) (N := N)).fv X = #0 ∈& (X + 1) := rfl


-- @@ L402-409 verbatim
@[simp] lemma q_free : (free (L := L) (ξ := ξ) (N := N))𐞥 = free := by
  ext X
  · cases X using Fin.cases
    · simp [free]
    case succ X =>
      simp
      cases X using Fin.lastCases <;> simp [-Fin.castSucc_succ, Fin.succ_castSucc]
  · simp [free]


-- @@ L411-411 verbatim
end free


-- @@ L413-415 verbatim
def rewrite (f : Ξ₁ → Ξ₂) : Rew L Ξ₁ N Ξ₂ N ξ where
  bv X := #0 ∈# X
  fv X := #0 ∈& f X


-- @@ L417-417 verbatim
section rewrite


-- @@ L419-420 verbatim
@[simp] lemma rewrite_bv (f : Ξ₁ → Ξ₂) (X : Fin N) :
    (rewrite (L := L) (ξ := ξ) f).bv X = #0 ∈# X := rfl


-- @@ L422-423 verbatim
@[simp] lemma rewrite_fv (f : Ξ₁ → Ξ₂) (X : Ξ₁) :
    (rewrite (L := L) (ξ := ξ) (N := N) f).fv X = #0 ∈& f X := rfl


-- @@ L425-429 verbatim
@[simp] lemma q_rewrite (f : Ξ₁ → Ξ₂) :
    (rewrite (L := L) (ξ := ξ) (N := N) f)𐞥 = rewrite f := by
  ext X
  · cases X using Fin.cases <;> simp [rewrite]
  · simp [rewrite]


-- @@ L431-431 verbatim
end rewrite


-- @@ L433-433 verbatim
def shift : Rew L ℕ N ℕ N ξ := rewrite (· + 1)


-- @@ L435-435 verbatim
section shift


-- @@ L437-438 verbatim
@[simp] lemma shift_bv (X : Fin N) :
    (shift (L := L) (ξ := ξ)).bv X = #0 ∈# X := rfl


-- @@ L440-441 verbatim
@[simp] lemma shift_fv (X : ℕ) :
    (shift (L := L) (ξ := ξ) (N := N)).fv X = #0 ∈& (X + 1) := rfl


-- @@ L443-444 verbatim
@[simp] lemma q_shift :
    (shift (L := L) (ξ := ξ) (N := N))𐞥 = shift := q_rewrite _


-- @@ L446-446 verbatim
end shift


-- @@ L448-448 verbatim
def emb {ο : Type*} [IsEmpty ο] : Rew L ο N Ξ N ξ := rewrite (IsEmpty.elim' inferInstance)


-- @@ L450-450 verbatim
section emb


-- @@ L452-452 verbatim
variable {ο : Type*} [IsEmpty ο]


-- @@ L454-455 verbatim
@[simp] lemma emb_bv (X : Fin N) :
    (emb (L := L) (ξ := ξ) (Ξ := Ξ) (ο := ο)).bv X = #0 ∈# X := rfl


-- @@ L457-458 verbatim
@[simp] lemma q_emb :
    (emb (L := L) (ξ := ξ) (Ξ := Ξ) (ο := ο) (N := N))𐞥 = emb := q_rewrite _


-- @@ L460-460 verbatim
end emb


-- @@ L462-464 verbatim
def subst (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) : Rew L Ξ₁ N₁ Ξ₁ N₂ ξ where
  bv := Φ
  fv X := #0 ∈& X


-- @@ L466-466 verbatim
section subst


-- @@ L468-469 verbatim
@[simp] lemma subst_bv (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) (X : Fin N₁) :
    (subst Φ).bv X = Φ X := rfl


-- @@ L471-478 verbatim
@[simp] lemma subst_fv (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) (X : Ξ₁) :
    (subst Φ).fv X = #0 ∈& X := rfl

lemma q_subst (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) :
    (subst Φ)𐞥 = subst ((#0 ∈# 0) :> fun X ↦ (Φ X).bmap .succ) := by
  ext X
  · cases X using Fin.cases <;> simp [subst]
  · simp [subst]


-- @@ L480-480 verbatim
end subst


-- @@ L482-482 verbatim
end Rew


-- @@ L484-484 verbatim
namespace Semiproposition


-- @@ L486-486 verbatim
abbrev free₀ (φ : Semiproposition L N (n + 1)) : Semiproposition L N n := FirstOrder.Rewriting.free φ


-- @@ L488-488 verbatim
abbrev shift₀ (φ : Semiproposition L N n) : Semiproposition L N n := FirstOrder.Rewriting.shift φ


-- @@ L490-490 verbatim
abbrev free₁ (φ : Semiproposition L (N + 1) n) : Semiproposition L N n := Rew.free.app φ


-- @@ L492-492 verbatim
abbrev shift₁ (φ : Semiproposition L N n) : Semiproposition L N n := Rew.shift.app φ


-- @@ L494-495 verbatim
abbrev subst₁ (φ : Semiformula L Ξ₁ ξ N₁ n) (Φ : Fin N₁ → Semiformula L Ξ₁ ξ N₂ 1) :
    Semiformula L Ξ₁ ξ N₂ n := (Rew.subst Φ).app φ


-- @@ L497-497 verbatim
section Notation


-- @@ L499-499 verbatim
open Lean PrettyPrinter Delaborator


-- @@ L501-501 verbatim
syntax (name := substNotation) term:max "/⟦" term,* "⟧" : term


-- @@ L503-504 verbatim
macro_rules (kind := substNotation)
  | `($φ:term /⟦$terms:term,*⟧) => `(subst₁ $φ ![$terms,*])


-- @@ L506-509 verbatim
@[app_unexpander subst₁]
meta def unexpsnderSubst : Unexpander
  | `($_ $φ:term ![$ts:term,*]) => `($φ /⟦ $ts,* ⟧)
  | _                           => throw ()


-- @@ L511-511 verbatim
end Notation


-- @@ L513-513 verbatim
end Semiproposition


-- @@ L515-515 verbatim
namespace Semisentence


-- @@ L517-517 verbatim
@[coe] abbrev emb (φ : Semisentence L N n) : Semiformula L Ξ ξ N n := Rew.emb.app (FirstOrder.Rewriting.emb φ)


-- @@ L519-519 verbatim
instance : Coe (Semisentence L N n) (Semiformula L Ξ ξ N n) := ⟨emb⟩


-- @@ L521-521 verbatim
end Semisentence


-- @@ L523-523 verbatim
end FFL.SecondOrder
