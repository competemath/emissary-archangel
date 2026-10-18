/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AnalyticSpace.LocalTupleRelations
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CocycleTwist
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentPushforwardClosedEmbedding


-- @@ L10-54 verbatim
/-!
# A reflexive hull criterion for coherence

Let `M` be a sheaf of `𝒪_Y`-modules on a locally ringed space `Y` whose structure sheaf has locally
finitely generated tuple relations (Oka's theorem). Let `U ⊆ Y` be open, `s₁, …, s_m ∈ M(U)`,
and `U₀ ⊆ U` open such that (`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData`)

* there are `𝒪`-linear functionals `τ₁, …, τ_{m'}` on `M` over opens of `U` which jointly
  separate sections (for bounded sections of a finite étale cover: `a ↦ tr(a sⱼ)`);
* for `V ⊆ U`, restriction `𝒪(V) → 𝒪(V ∩ U₀)` is bijective and `M(V) → M(V ∩ U₀)` is surjective
  (Hartogs extension across `U ∖ U₀`);
* near every point of `U₀`, `M` is free with a basis in the span of the `sᵢ`.

Then `M` is coherent on `U`, and `M` is coherent if such data exist near every point
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_reflexiveHullData`).

## Proof

Let `M' ⊆ M` be the image of `𝒪^m → M`, `eᵢ ↦ sᵢ`. Its relations are the tuple relations of the
values `τ_j(sᵢ)`, so they are locally finitely generated. By Oka's theorem, near a point `x₀ ∈ U`
there are vectors `λ_p ∈ 𝒪^m` generating the vectors annihilating all relations of the `sᵢ`
(this is `Hom(M', 𝒪)`), generators `ρ_l` of the relations of the `λ_p`, and generators `ε_l` of
the vectors annihilating the `ρ_l` (this is `Hom(Hom(M', 𝒪), 𝒪)`)
(`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData.LocalData`).

Evaluation at the `λ_p` identifies `M` with `M'^{**}`: a section `a` of `M` over `V` is, near
every point of `U₀`, a combination `∑ fᵢ sᵢ`, and `(∑ᵢ λ_{p,i} fᵢ)_p` is well defined there; by
Hartogs extension for `𝒪` it extends to `V`
(`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData.LocalData.exists_rel`). This evaluation
is injective, as the Gram vectors `(τ_j(sᵢ))ᵢ` are combinations of the `λ_p`
(`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData.LocalData.Rel.eq_zero`), and its image
consists of the vectors annihilating the `ρ_l`: this is the reflexivity of the free module `M`
near points of `U₀`, and preimages glue and extend by Hartogs extension for `M`
(`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData.LocalData.exists_rel_of`). Hence the
preimages of the `ε_l` generate `M` near `x₀`
(`AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData.LocalData.exists_generators`).

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.ReflexiveHullData M U`: the data above on `U`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_reflexiveHullData`: the criterion.
-/


-- @@ L56-56 verbatim
open CategoryTheory Opposite TopologicalSpace


-- @@ L58-58 verbatim
universe u


-- @@ L60-60 verbatim
noncomputable section


-- @@ L62-62 verbatim
namespace AlgebraicGeometry.LocallyRingedSpace


-- @@ L64-64 verbatim
variable {Y : LocallyRingedSpace.{u}}


-- @@ L66-68 verbatim
set_option hygiene false in
/-- Sections of the structure sheaf of `Y` over `W`. -/
local notation "Γᵧ(" W ")" => Y.presheaf.obj (op W)


-- @@ L70-70 verbatim
/-! ### Local equality and gluing -/


-- @@ L72-72 verbatim
section Local


-- @@ L74-74 verbatim
variable (M : SheafOfModules.{u} Y.ringSheaf)


-- @@ L76-83 verbatim
/-- Sections of a sheaf of modules which agree near every point agree. -/
lemma sectRes_eq_of_locally {W : Opens Y} {s t : M.val.obj (op W)}
    (h : ∀ y ∈ W, ∃ (W' : Opens Y) (hW' : W' ≤ W), y ∈ W' ∧ sectRes M hW' s = sectRes M hW' t) :
    s = t := by
  choose O hO hyO hst using h
  exact modRes_eq_of_cover M (fun y : W ↦ O y.1 y.2)
    (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyO y hy⟩) (fun y ↦ hO y.1 y.2) s t
    fun y ↦ hst y.1 y.2


-- @@ L85-89 verbatim
/-- Sections of the structure sheaf which agree near every point agree. -/
lemma res_eq_of_locally {W : Opens Y} {s t : Γᵧ(W)}
    (h : ∀ y ∈ W, ∃ (W' : Opens Y) (hW' : W' ≤ W), y ∈ W' ∧ Y.res hW' s = Y.res hW' t) :
    s = t :=
  sectRes_eq_of_locally (SheafOfModules.unit Y.ringSheaf) h


-- @@ L91-101 verbatim
/-- **Gluing** sections of a sheaf of modules given near every point, which agree on overlaps. -/
lemma exists_sectRes_eq_of_locally {W : Opens Y} (O : ∀ y ∈ W, Opens Y)
    (hO : ∀ y hy, O y hy ≤ W) (hyO : ∀ y hy, y ∈ O y hy)
    (t : ∀ y hy, M.val.obj (op (O y hy)))
    (ht : ∀ y hy z hz, sectRes M (inf_le_left : O y hy ⊓ O z hz ≤ O y hy) (t y hy) =
      sectRes M (inf_le_right : O y hy ⊓ O z hz ≤ O z hz) (t z hz)) :
    ∃ s : M.val.obj (op W), ∀ y hy, sectRes M (hO y hy) s = t y hy := by
  obtain ⟨s, hs, -⟩ := modRes_existsUnique_gluing M (fun y : W ↦ O y.1 y.2)
    (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyO y hy⟩) (fun y ↦ hO y.1 y.2)
    (fun y ↦ t y.1 y.2) fun y z ↦ ht y.1 y.2 z.1 z.2
  exact ⟨s, fun y hy ↦ hs ⟨y, hy⟩⟩


-- @@ L103-103 verbatim
end Local

-- @@ L104-104 verbatim
/-! ### The data -/


-- @@ L106-137 verbatim
/-- **Data for the reflexive hull criterion** on an open `U`: sections `s₁, …, s_m` of `M` over
`U`; `𝒪`-linear functionals `τ₁, …, τ_{m'}` on the sections of `M` over opens inside `U`,
compatible with restriction, which jointly separate sections; and an open `U₀ ⊆ U` such that for
every open `V ⊆ U` restriction `𝒪_Y(V) → 𝒪_Y(V ∩ U₀)` is bijective and `M(V) → M(V ∩ U₀)` is
surjective, and such that near every point of `U₀` the sheaf `M` is free with a basis in the span
of the `sᵢ`. -/
structure ReflexiveHullData (M : SheafOfModules.{u} Y.ringSheaf) (U : Opens Y) where
  /-- The open part of `U` where `M` is locally free. -/
  U₀ : Opens Y
  le : U₀ ≤ U
  /-- The number of sections. -/
  m : ℕ
  /-- The sections. -/
  s : Fin m → M.val.obj (op U)
  /-- The number of functionals. -/
  m' : ℕ
  /-- The functionals. -/
  τ : Fin m' → ∀ V : Opens Y, V ≤ U → M.val.obj (op V) → Γᵧ(V)
  τ_add : ∀ j V hV (a b : M.val.obj (op V)), τ j V hV (a + b) = τ j V hV a + τ j V hV b
  τ_smul : ∀ j V hV (r : Γᵧ(V)) (a : M.val.obj (op V)), τ j V hV (r • a) = r * τ j V hV a
  τ_res : ∀ j V hV V' (h : V' ≤ V) (a : M.val.obj (op V)),
    τ j V' (h.trans hV) (sectRes M h a) = Y.res h (τ j V hV a)
  eq_zero_of_τ : ∀ V hV (a : M.val.obj (op V)), (∀ j, τ j V hV a = 0) → a = 0
  injective_res : ∀ V, V ≤ U → Function.Injective (Y.res (inf_le_left : V ⊓ U₀ ≤ V))
  surjective_res : ∀ V, V ≤ U → Function.Surjective (Y.res (inf_le_left : V ⊓ U₀ ≤ V))
  surjective_sectRes : ∀ V, V ≤ U →
    Function.Surjective (sectRes M (inf_le_left : V ⊓ U₀ ≤ V))
  exists_basis : ∀ y ∈ U₀, ∃ (V : Opens Y) (hVU : V ≤ U) (r : ℕ) (e : Fin r → M.val.obj (op V))
    (P : Fin r → Fin m → Γᵧ(V)), y ∈ V ∧ (∀ k, e k = ∑ i, P k i • sectRes M hVU (s i)) ∧
    (∀ V' (h : V' ≤ V) (a : M.val.obj (op V')),
      ∃ c : Fin r → Γᵧ(V'), a = ∑ k, c k • sectRes M h (e k)) ∧
    ∀ V' (h : V' ≤ V) (c : Fin r → Γᵧ(V')), ∑ k, c k • sectRes M h (e k) = 0 → ∀ k, c k = 0


-- @@ L139-139 verbatim
namespace ReflexiveHullData


-- @@ L141-141 verbatim
variable {M : SheafOfModules.{u} Y.ringSheaf} {U : Opens Y} (D : ReflexiveHullData M U)


-- @@ L143-144 verbatim
lemma τ_zero (j : Fin D.m') {V : Opens Y} (hV : V ≤ U) : D.τ j V hV 0 = 0 := by
  simpa using D.τ_smul j V hV 0 0


-- @@ L146-155 verbatim
lemma τ_sum_smul (j : Fin D.m') {V : Opens Y} (hV : V ≤ U) {k : ℕ} (a : Fin k → Γᵧ(V))
    (f : Fin k → M.val.obj (op V)) : D.τ j V hV (∑ i, a i • f i) = ∑ i, a i * D.τ j V hV (f i) := by
  classical
  have : ∀ s : Finset (Fin k), D.τ j V hV (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, a i * D.τ j V hV (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using D.τ_zero j hV
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, D.τ_add, D.τ_smul, ih]
  exact this Finset.univ


-- @@ L157-167 verbatim
/-- A combination of sections vanishes if and only if all functionals of it vanish. -/
lemma sum_smul_eq_zero_iff {V : Opens Y} (hV : V ≤ U) {W : Opens Y} (hW : W ≤ V) {k : ℕ}
    (f : Fin k → M.val.obj (op V)) (a : Fin k → Γᵧ(W)) :
    ∑ i, a i • sectRes M hW (f i) = 0 ↔
      ∀ j, ∑ i, a i * Y.res hW (D.τ j V hV (f i)) = 0 := by
  have key : ∀ j, D.τ j W (hW.trans hV) (∑ i, a i • sectRes M hW (f i)) =
      ∑ i, a i * Y.res hW (D.τ j V hV (f i)) := fun j ↦ by
    rw [D.τ_sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [D.τ_res]
  refine ⟨fun h j ↦ ?_, fun h ↦ D.eq_zero_of_τ W (hW.trans hV) _ fun j ↦ (key j).trans (h j)⟩
  rw [← key, h, D.τ_zero]


-- @@ L169-185 verbatim
include D in
/-- **Relations of sections of `M` inside `U` are locally finitely generated**: they are the
tuple relations of the values of the functionals. -/
theorem exists_relations (hO : HasLocalTupleRelations (SheafOfModules.unit Y.ringSheaf))
    {V : Opens Y} (hV : V ≤ U) {k : ℕ} (f : Fin k → M.val.obj (op V)) {x : Y} (hx : x ∈ V) :
    ∃ (W : Opens Y) (hWV : W ≤ V) (q : ℕ) (g : Fin q → Fin k → Γᵧ(W)),
      x ∈ W ∧ (∀ l, ∑ i, g l i • sectRes M hWV (f i) = 0) ∧
      ∀ (W' : Opens Y) (hW' : W' ≤ W) (a : Fin k → Γᵧ(W')),
        (∑ i, a i • sectRes M (hW'.trans hWV) (f i) = 0) → ∀ y ∈ W',
          ∃ (W'' : Opens Y) (hW'' : W'' ≤ W'), y ∈ W'' ∧ ∃ c : Fin q → Γᵧ(W''),
            ∀ i, Y.res hW'' (a i) = ∑ l, c l * Y.res (hW''.trans hW') (g l i) := by
  obtain ⟨W, hWV, q, g, hxW, hg, hgen⟩ :=
    hO V k D.m' (fun i j ↦ (D.τ j V hV (f i) : Γᵧ(V))) x hx
  refine ⟨W, hWV, q, g, hxW, fun l ↦ (D.sum_smul_eq_zero_iff hV hWV f (g l)).2 (hg l),
    fun W' hW' a ha ↦ hgen W' hW' a fun j ↦ ?_⟩
  have := (D.sum_smul_eq_zero_iff hV (hW'.trans hWV) f a).1 ha j
  exact this


-- @@ L187-191 verbatim
/-- `μ` **annihilates the relations** of the `sᵢ`: `∑ μᵢ fᵢ = 0` for every relation
`∑ fᵢ sᵢ = 0` over an open inside `W`. -/
def Annihilates {W : Opens Y} (hW : W ≤ U) (μ : Fin D.m → Γᵧ(W)) : Prop :=
  ∀ (W' : Opens Y) (h : W' ≤ W) (f : Fin D.m → Γᵧ(W')),
    ∑ i, f i • sectRes M (h.trans hW) (D.s i) = 0 → ∑ i, Y.res h (μ i) * f i = 0


-- @@ L193-197 verbatim
variable {D} in
lemma Annihilates.res {W : Opens Y} {hW : W ≤ U} {μ : Fin D.m → Γᵧ(W)}
    (hμ : D.Annihilates hW μ) {W' : Opens Y} (h : W' ≤ W) :
    D.Annihilates (h.trans hW) (fun i ↦ Y.res h (μ i)) := fun W'' h' f hf ↦ by
  simpa only [res_res] using hμ W'' (h'.trans h) f hf


-- @@ L199-199 verbatim
end ReflexiveHullData


-- @@ L201-205 verbatim
/-- `a` is, **near every point**, an `𝒪`-combination of the restrictions of the `g l`. -/
def IsLocalCombination {W W' : Opens Y} (h : W' ≤ W) {q k : ℕ} (g : Fin q → Fin k → Γᵧ(W))
    (a : Fin k → Γᵧ(W')) : Prop :=
  ∀ y ∈ W', ∃ (W'' : Opens Y) (hW'' : W'' ≤ W'), y ∈ W'' ∧ ∃ c : Fin q → Γᵧ(W''),
    ∀ i, Y.res hW'' (a i) = ∑ l, c l * Y.res (hW''.trans h) (g l i)


-- @@ L207-211 verbatim
lemma isLocalCombination_res_iff {W₀ W W' : Opens Y} (h₀ : W ≤ W₀) (h : W' ≤ W) {q k : ℕ}
    (g : Fin q → Fin k → Γᵧ(W₀)) (a : Fin k → Γᵧ(W')) :
    IsLocalCombination h (fun l i ↦ Y.res h₀ (g l i)) a ↔
      IsLocalCombination (h.trans h₀) g a := by
  simp only [IsLocalCombination, res_res]


-- @@ L213-226 verbatim
/-- A section of the structure sheaf which is locally a combination of sections which are zero
against a fixed vector is zero against it. -/
lemma IsLocalCombination.sum_mul_eq_zero {W W' : Opens Y} {h : W' ≤ W} {q k : ℕ}
    {g : Fin q → Fin k → Γᵧ(W)} {a : Fin k → Γᵧ(W')} (ha : IsLocalCombination h g a)
    (b : Fin k → Γᵧ(W')) (hg : ∀ l, ∑ i, Y.res h (g l i) * b i = 0) :
    ∑ i, a i * b i = 0 := by
  refine res_eq_of_locally fun y hy ↦ ?_
  obtain ⟨W'', hW'', hy'', c, hc⟩ := ha y hy
  refine ⟨W'', hW'', hy'', ?_⟩
  have e : Y.res hW'' (∑ i, a i * b i) = ∑ l, c l * Y.res hW'' (∑ i, Y.res h (g l i) * b i) := by
    simp only [res_sum, res_mul, hc, res_res, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [e, res_zero]
  exact Finset.sum_eq_zero fun l _ ↦ by rw [hg l, res_zero, mul_zero]


-- @@ L228-228 verbatim
namespace ReflexiveHullData


-- @@ L230-230 verbatim
variable {M : SheafOfModules.{u} Y.ringSheaf} {U : Opens Y} (D : ReflexiveHullData M U)


-- @@ L232-261 verbatim
/-- **The local data at `x₀`**: an open `W ∋ x₀` inside `U` and vectors `λ_p ∈ 𝒪(W)^m`
generating the vectors annihilating the relations of the `sᵢ` (the dual of the image of
`𝒪^m → M`), with generators `ρ_l` of the relations of the `λ_p` and generators `ε_l` of the
vectors annihilating the `ρ_l`. -/
structure LocalData (x₀ : Y) where
  /-- The open. -/
  W : Opens Y
  le : W ≤ U
  mem : x₀ ∈ W
  /-- The number of the `λ_p`. -/
  q : ℕ
  /-- Generators of the vectors annihilating the relations of the `sᵢ`. -/
  lam : Fin q → Fin D.m → Γᵧ(W)
  annihilates_lam : ∀ p, D.Annihilates le (lam p)
  gen_lam : ∀ (W' : Opens Y) (h : W' ≤ W) (μ : Fin D.m → Γᵧ(W')),
    D.Annihilates (h.trans le) μ → IsLocalCombination h lam μ
  /-- The number of the `ρ_l`. -/
  q' : ℕ
  /-- Generators of the relations of the `λ_p`. -/
  ρ : Fin q' → Fin q → Γᵧ(W)
  rel_ρ : ∀ l i, ∑ p, ρ l p * lam p i = 0
  gen_ρ : ∀ (W' : Opens Y) (h : W' ≤ W) (t : Fin q → Γᵧ(W')),
    (∀ i, ∑ p, t p * Y.res h (lam p i) = 0) → IsLocalCombination h ρ t
  /-- The number of the `ε_l`. -/
  q'' : ℕ
  /-- Generators of the vectors annihilating the `ρ_l`. -/
  ε : Fin q'' → Fin q → Γᵧ(W)
  rel_ε : ∀ l' l, ∑ p, ε l' p * ρ l p = 0
  gen_ε : ∀ (W' : Opens Y) (h : W' ≤ W) (v : Fin q → Γᵧ(W')),
    (∀ l, ∑ p, v p * Y.res h (ρ l p) = 0) → IsLocalCombination h ε v


-- @@ L263-270 verbatim
/-- Oka's theorem for tuples of sections of the structure sheaf, in the form used below. -/
lemma exists_tuple_relations (hO : HasLocalTupleRelations (SheafOfModules.unit Y.ringSheaf))
    {V : Opens Y} {q k : ℕ} (v : Fin q → Fin k → Γᵧ(V)) {x : Y} (hx : x ∈ V) :
    ∃ (W : Opens Y) (hWV : W ≤ V) (p : ℕ) (g : Fin p → Fin q → Γᵧ(W)), x ∈ W ∧
      (∀ l j, ∑ i, g l i * Y.res hWV (v i j) = 0) ∧
      ∀ (W' : Opens Y) (hW' : W' ≤ W) (a : Fin q → Γᵧ(W')),
        (∀ j, ∑ i, a i * Y.res (hW'.trans hWV) (v i j) = 0) → IsLocalCombination hW' g a :=
  hO V q k v x hx


-- @@ L272-312 verbatim
/-- The local data exist at every point of `U`, by Oka's theorem for tuples. -/
theorem nonempty_localData (hO : HasLocalTupleRelations (SheafOfModules.unit Y.ringSheaf))
    {x₀ : Y} (hx₀ : x₀ ∈ U) : Nonempty (D.LocalData x₀) := by
  obtain ⟨W₁, h₁, r₁, κ, hx₁, hκ, hκgen⟩ := D.exists_relations hO le_rfl D.s hx₀
  obtain ⟨W₂, h₂, q, lam, hx₂, hlam, hlamgen⟩ :=
    exists_tuple_relations hO (fun i l ↦ (κ l i : Γᵧ(W₁))) hx₁
  obtain ⟨W₃, h₃, q', ρ, hx₃, hρ, hρgen⟩ :=
    exists_tuple_relations hO (fun p i ↦ (lam p i : Γᵧ(W₂))) hx₂
  obtain ⟨W₄, h₄, q'', ε, hx₄, hε, hεgen⟩ :=
    exists_tuple_relations hO (fun p l ↦ (ρ l p : Γᵧ(W₃))) hx₃
  -- `λ_p` annihilates the relations
  have hann : ∀ p, D.Annihilates (h₂.trans h₁) (lam p) := fun p W' h f hf ↦ by
    rw [show ∑ i, Y.res h (lam p i) * f i = ∑ i, f i * Y.res h (lam p i) from
      Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    refine IsLocalCombination.sum_mul_eq_zero (h := h.trans h₂) (hκgen W' (h.trans h₂) f hf) _
      fun l ↦ ?_
    have := congrArg (Y.res h) (hlam p l)
    simp only [res_sum, res_mul, res_res, res_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  -- a vector annihilating the relations is a combination of the `λ_p`
  have hgen : ∀ (W' : Opens Y) (h : W' ≤ W₂) (μ : Fin D.m → Γᵧ(W')),
      D.Annihilates ((h.trans h₂).trans h₁) μ → IsLocalCombination h lam μ := fun W' h μ hμ ↦ by
    refine hlamgen W' h μ fun l ↦ ?_
    have hrel : ∑ i, Y.res (h.trans h₂) (κ l i) • sectRes M ((h.trans h₂).trans h₁) (D.s i) =
        0 := by
      have := congrArg (sectRes M (h.trans h₂)) (hκ l)
      simpa only [sectRes_sum_smul, sectRes_sectRes, sectRes_zero] using this
    have := hμ W' le_rfl _ hrel
    simpa only [res_self, mul_comm] using this
  refine ⟨⟨W₄, ((h₄.trans h₃).trans h₂).trans h₁, hx₄, q,
    fun p i ↦ Y.res (h₄.trans h₃) (lam p i), fun p ↦ ?_, fun W' h μ hμ ↦ ?_, q',
    fun l p ↦ Y.res h₄ (ρ l p), fun l i ↦ ?_, fun W' h t ht ↦ ?_, q'', ε, hε,
    fun W' h v hv ↦ hεgen W' h v fun l ↦ by simpa only [res_res] using hv l⟩⟩
  · exact (hann p).res (h₄.trans h₃)
  · rw [isLocalCombination_res_iff]
    exact hgen W' (h.trans (h₄.trans h₃)) μ hμ
  · have := congrArg (Y.res h₄) (hρ l i)
    simpa only [res_sum, res_mul, res_res, res_zero] using this
  · rw [isLocalCombination_res_iff]
    exact hρgen W' (h.trans h₄) t fun i ↦ by simpa only [res_res] using ht i


-- @@ L314-323 verbatim
/-- Near every point of `U₀`, every section of `M` is a combination of the `sᵢ`. -/
lemma exists_span {y : Y} (hy : y ∈ D.U₀) : ∃ (V : Opens Y) (hVU : V ≤ U), y ∈ V ∧
    ∀ (V' : Opens Y) (h : V' ≤ V) (a : M.val.obj (op V')),
      ∃ f : Fin D.m → Γᵧ(V'), a = ∑ i, f i • sectRes M (h.trans hVU) (D.s i) := by
  obtain ⟨V, hVU, r, e, P, hyV, he, hspan, -⟩ := D.exists_basis y hy
  refine ⟨V, hVU, hyV, fun V' h a ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hspan V' h a
  refine ⟨fun i ↦ ∑ k, c k * Y.res h (P k i), ?_⟩
  simp only [he, sectRes_sum_smul, sectRes_sectRes, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm


-- @@ L325-335 verbatim
/-- The vectors annihilating the relations of the `sᵢ` give equal values on two representations
of the same section. -/
lemma sum_mul_eq_of_annihilates {W : Opens Y} {hW : W ≤ U} {μ : Fin D.m → Γᵧ(W)}
    (hμ : D.Annihilates hW μ) {V : Opens Y} (h : V ≤ W) {f f' : Fin D.m → Γᵧ(V)}
    (hff' : ∑ i, f i • sectRes M (h.trans hW) (D.s i) =
      ∑ i, f' i • sectRes M (h.trans hW) (D.s i)) :
    ∑ i, Y.res h (μ i) * f i = ∑ i, Y.res h (μ i) * f' i := by
  have := hμ V h (f - f') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hff', sub_self])
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at this
  exact sub_eq_zero.1 this



-- @@ L338-339 verbatim
lemma sectRes_refl {V : Opens Y} (a : M.val.obj (op V)) : sectRes M le_rfl a = a :=
  modRes_self a


-- @@ L341-346 verbatim
private lemma sum_comm₃ {R : Type*} [AddCommMonoid R] {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → R) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c :=
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, F a b c := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := Finset.sum_comm


-- @@ L348-378 verbatim
/-- The linear algebra behind the local surjectivity: with `Q = D λ` (`F1`), `λ (Q P) = λ`
(`F2`) and `v` annihilating the relations of the `λ_p` (`F3`), the vector `v` is recovered from
`φ = D v` as `v_p = ∑ᵢ λ_{p,i} ∑ₖ φₖ P_{k,i}`. -/
private lemma sum_eq_of_relations {R : Type*} [CommRing R] {q m r : ℕ} (lamR : Fin q → Fin m → R)
    (PR : Fin r → Fin m → R) (QR : Fin m → Fin r → R) (Dc : Fin r → Fin q → R) (vR : Fin q → R)
    (F1 : ∀ i k, QR i k = ∑ p, Dc k p * lamR p i)
    (F2 : ∀ p i, ∑ i', lamR p i' * ∑ k, QR i k * PR k i' = lamR p i)
    (F3 : ∀ t : Fin q → R, (∀ i, ∑ p, t p * lamR p i = 0) → ∑ p, t p * vR p = 0) (p : Fin q) :
    vR p = ∑ i, lamR p i * ∑ k, (∑ p', Dc k p' * vR p') * PR k i := by
  classical
  set t : Fin q → R := fun p' ↦ ∑ k, (∑ i, lamR p i * PR k i) * Dc k p' -
    if p' = p then 1 else 0
  have ht : ∀ i, ∑ p', t p' * lamR p' i = 0 := fun i ↦ by
    simp only [t, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← F2 p i]
    simp only [F1, Finset.sum_mul, Finset.mul_sum]
    rw [sum_comm₃]
    refine Finset.sum_congr rfl fun i' _ ↦ Finset.sum_congr rfl fun k _ ↦
      Finset.sum_congr rfl fun p' _ ↦ ?_
    ring
  have := F3 t ht
  simp only [t, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [sub_eq_zero] at this
  rw [← this]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm₃]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
    Finset.sum_congr rfl fun p' _ ↦ ?_
  ring

-- @@ L379-379 verbatim
namespace LocalData


-- @@ L381-381 verbatim
variable {D} {x₀ : Y} (L : D.LocalData x₀)


-- @@ L383-388 verbatim
/-- `v` is the image of `a` under the evaluation `a ↦ (λ_p(a))_p`: near every point of
`V ∩ U₀`, `a = ∑ fᵢ sᵢ` with `v_p = ∑ λ_{p,i} fᵢ`. -/
def Rel {V : Opens Y} (hV : V ≤ L.W) (a : M.val.obj (op V)) (v : Fin L.q → Γᵧ(V)) : Prop :=
  ∀ y ∈ V ⊓ D.U₀, ∃ (V₁ : Opens Y) (h₁ : V₁ ≤ V), y ∈ V₁ ∧ ∃ f : Fin D.m → Γᵧ(V₁),
    sectRes M h₁ a = ∑ i, f i • sectRes M ((h₁.trans hV).trans L.le) (D.s i) ∧
    ∀ p, Y.res h₁ (v p) = ∑ i, Y.res (h₁.trans hV) (L.lam p i) * f i


-- @@ L390-390 verbatim
variable {V : Opens Y} (hV : V ≤ L.W)


-- @@ L392-401 verbatim
variable {L hV} in
lemma Rel.res {a : M.val.obj (op V)} {v : Fin L.q → Γᵧ(V)} (h : L.Rel hV a v) {V' : Opens Y}
    (hV' : V' ≤ V) : L.Rel (hV'.trans hV) (sectRes M hV' a) (fun p ↦ Y.res hV' (v p)) := by
  intro y hy
  obtain ⟨V₁, h₁, hy₁, f, ha, hv⟩ := h y ⟨hV' hy.1, hy.2⟩
  refine ⟨V₁ ⊓ V', inf_le_right, ⟨hy₁, hy.1⟩, fun i ↦ Y.res inf_le_left (f i), ?_, fun p ↦ ?_⟩
  · have := congrArg (sectRes M (inf_le_left : V₁ ⊓ V' ≤ V₁)) ha
    simpa only [sectRes_sectRes, sectRes_sum_smul] using this
  · have := congrArg (Y.res (inf_le_left : V₁ ⊓ V' ≤ V₁)) (hv p)
    simpa only [res_res, res_sum, res_mul] using this


-- @@ L403-404 verbatim
lemma rel_zero : L.Rel hV 0 0 := fun y hy ↦
  ⟨V, le_rfl, hy.1, 0, by simp [sectRes_zero], fun p ↦ by simp⟩


-- @@ L406-427 verbatim
variable {L hV} in
lemma Rel.add {a b : M.val.obj (op V)} {v w : Fin L.q → Γᵧ(V)} (ha : L.Rel hV a v)
    (hb : L.Rel hV b w) : L.Rel hV (a + b) (v + w) := by
  intro y hy
  obtain ⟨V₁, h₁, hy₁, f, hfa, hfv⟩ := ha y hy
  obtain ⟨V₂, h₂, hy₂, g, hgb, hgw⟩ := hb y hy
  refine ⟨V₁ ⊓ V₂, inf_le_left.trans h₁, ⟨hy₁, hy₂⟩,
    fun i ↦ Y.res inf_le_left (f i) + Y.res inf_le_right (g i), ?_, fun p ↦ ?_⟩
  · have e₁ := congrArg (sectRes M (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) hfa
    have e₂ := congrArg (sectRes M (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) hgb
    simp only [sectRes_sectRes, sectRes_sum_smul] at e₁ e₂
    rw [show sectRes M (inf_le_left.trans h₁) (a + b) =
      sectRes M (inf_le_left.trans h₁) a + sectRes M (inf_le_right.trans h₂) b from
        map_add _ _ _, e₁, e₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (add_smul _ _ _).symm
  · have e₁ := congrArg (Y.res (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) (hfv p)
    have e₂ := congrArg (Y.res (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) (hgw p)
    simp only [res_res, res_sum, res_mul] at e₁ e₂
    rw [Pi.add_apply, show Y.res (inf_le_left.trans h₁) (v p + w p) =
      Y.res (inf_le_left.trans h₁) (v p) + Y.res (inf_le_right.trans h₂) (w p) from
        map_add _ _ _, e₁, e₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (mul_add _ _ _).symm


-- @@ L429-438 verbatim
variable {L hV} in
lemma Rel.smul {a : M.val.obj (op V)} {v : Fin L.q → Γᵧ(V)} (ha : L.Rel hV a v) (r : Γᵧ(V)) :
    L.Rel hV (r • a) (fun p ↦ r * v p) := by
  intro y hy
  obtain ⟨V₁, h₁, hy₁, f, hfa, hfv⟩ := ha y hy
  refine ⟨V₁, h₁, hy₁, fun i ↦ Y.res h₁ r * f i, ?_, fun p ↦ ?_⟩
  · rw [sectRes_smul, hfa, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (mul_smul _ _ _).symm
  · rw [res_mul, hfv p, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring


-- @@ L440-445 verbatim
variable {L hV} in
lemma Rel.sub {a b : M.val.obj (op V)} {v w : Fin L.q → Γᵧ(V)} (ha : L.Rel hV a v)
    (hb : L.Rel hV b w) : L.Rel hV (a - b) (v - w) := by
  have := ha.add (hb.smul (-1))
  simp only [neg_one_smul, neg_one_mul] at this
  rwa [sub_eq_add_neg, sub_eq_add_neg]


-- @@ L447-458 verbatim
lemma rel_sum {ι : Type*} (t : Finset ι) (c : ι → Γᵧ(V)) (a : ι → M.val.obj (op V))
    (v : ι → Fin L.q → Γᵧ(V)) (h : ∀ i ∈ t, L.Rel hV (a i) (v i)) :
    L.Rel hV (∑ i ∈ t, c i • a i) (fun p ↦ ∑ i ∈ t, c i * v i p) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact L.rel_zero hV
  | insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((h j (Finset.mem_insert_self j t)).smul (c j)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))


-- @@ L460-465 verbatim
/-- Two representations of the same section give the same values of the `λ_p`. -/
lemma sum_lam_eq {V₁ : Opens Y} (h₁ : V₁ ≤ L.W) {f g : Fin D.m → Γᵧ(V₁)}
    (hfg : ∑ i, f i • sectRes M (h₁.trans L.le) (D.s i) =
      ∑ i, g i • sectRes M (h₁.trans L.le) (D.s i)) (p : Fin L.q) :
    ∑ i, Y.res h₁ (L.lam p i) * f i = ∑ i, Y.res h₁ (L.lam p i) * g i :=
  D.sum_mul_eq_of_annihilates (L.annihilates_lam p) h₁ hfg


-- @@ L467-485 verbatim
variable {L hV} in
lemma Rel.eq {a : M.val.obj (op V)} {v v' : Fin L.q → Γᵧ(V)} (h : L.Rel hV a v)
    (h' : L.Rel hV a v') : v = v' := by
  funext p
  refine D.injective_res V (hV.trans L.le) (res_eq_of_locally fun y hy ↦ ?_)
  obtain ⟨V₁, h₁, hy₁, f, hfa, hfv⟩ := h y hy
  obtain ⟨V₂, h₂, hy₂, g, hga, hgv⟩ := h' y hy
  have k₁ : V₁ ⊓ V₂ ⊓ D.U₀ ≤ V₁ := inf_le_left.trans inf_le_left
  have k₂ : V₁ ⊓ V₂ ⊓ D.U₀ ≤ V₂ := inf_le_left.trans inf_le_right
  refine ⟨V₁ ⊓ V₂ ⊓ D.U₀, le_inf (k₁.trans h₁) inf_le_right, ⟨⟨hy₁, hy₂⟩, hy.2⟩, ?_⟩
  have e₁ := congrArg (Y.res k₁) (hfv p)
  have e₂ := congrArg (Y.res k₂) (hgv p)
  simp only [res_res, res_sum, res_mul] at e₁ e₂ ⊢
  rw [e₁, e₂]
  refine L.sum_lam_eq ((k₁.trans h₁).trans hV) ?_ p
  have a₁ := congrArg (sectRes M k₁) hfa
  have a₂ := congrArg (sectRes M k₂) hga
  simp only [sectRes_sectRes, sectRes_sum_smul] at a₁ a₂
  exact a₁.symm.trans a₂


-- @@ L487-514 verbatim
/-- **Every section has an image under the evaluation at the `λ_p`**: the local values glue
over `V ∩ U₀` and extend to `V`. -/
lemma exists_rel (a : M.val.obj (op V)) : ∃ v, L.Rel hV a v := by
  classical
  choose Vs hVsU hyVs hspan using fun (y : Y) (hy : y ∈ V ⊓ D.U₀) ↦ D.exists_span hy.2
  -- the local representations over `Vs y ⊓ V ⊓ U₀`
  set O : ∀ y ∈ V ⊓ D.U₀, Opens Y := fun y hy ↦ Vs y hy ⊓ (V ⊓ D.U₀)
  have hOV : ∀ y hy, O y hy ≤ V ⊓ D.U₀ := fun y hy ↦ inf_le_right
  have hOV' : ∀ y hy, O y hy ≤ V := fun y hy ↦ (hOV y hy).trans inf_le_left
  have hOVs : ∀ y hy, O y hy ≤ Vs y hy := fun y hy ↦ inf_le_left
  choose f hf using fun y hy ↦ hspan y hy (O y hy) (hOVs y hy) (sectRes M (hOV' y hy) a)
  have hv : ∀ p, ∃ v₀ : Γᵧ(V ⊓ D.U₀), ∀ y hy, Y.res (hOV y hy) v₀ =
      ∑ i, Y.res ((hOV' y hy).trans hV) (L.lam p i) * f y hy i := fun p ↦ by
    refine exists_sectRes_eq_of_locally (SheafOfModules.unit Y.ringSheaf) O hOV
      (fun y hy ↦ ⟨hyVs y hy, hy⟩) _ fun y hy z hz ↦ ?_
    change Y.res inf_le_left (∑ i, Y.res ((hOV' y hy).trans hV) (L.lam p i) * f y hy i) =
      Y.res inf_le_right (∑ i, Y.res ((hOV' z hz).trans hV) (L.lam p i) * f z hz i)
    simp only [res_sum, res_mul, res_res]
    refine L.sum_lam_eq ((inf_le_left.trans (hOV' y hy)).trans hV) ?_ p
    have a₁ := congrArg (sectRes M (inf_le_left : O y hy ⊓ O z hz ≤ O y hy)) (hf y hy)
    have a₂ := congrArg (sectRes M (inf_le_right : O y hy ⊓ O z hz ≤ O z hz)) (hf z hz)
    simp only [sectRes_sectRes, sectRes_sum_smul] at a₁ a₂
    exact a₁.symm.trans a₂
  choose v₀ hv₀ using hv
  choose v hvv₀ using fun p ↦ D.surjective_res V (hV.trans L.le) (v₀ p)
  refine ⟨v, fun y hy ↦ ⟨O y hy, hOV' y hy, ⟨hyVs y hy, hy⟩, f y hy, ?_, fun p ↦ ?_⟩⟩
  · exact hf y hy
  · rw [← hv₀ p y hy, ← hvv₀ p, res_res]


-- @@ L516-544 verbatim
variable {L hV} in
/-- **The evaluation at the `λ_p` is injective.** The Gram vectors `(τ_j(sᵢ))ᵢ` annihilate the
relations of the `sᵢ`, so they are combinations of the `λ_p`, hence all `τ_j` vanish on a
section whose values at the `λ_p` vanish. -/
lemma Rel.eq_zero {a : M.val.obj (op V)} (h : L.Rel hV a 0) : a = 0 := by
  refine D.eq_zero_of_τ V (hV.trans L.le) a fun j ↦ ?_
  refine D.injective_res V (hV.trans L.le) (res_eq_of_locally fun y hy ↦ ?_)
  obtain ⟨V₁, h₁, hy₁, f, hfa, hfv⟩ := h y hy
  set γ : Fin D.m → Γᵧ(L.W) := fun i ↦ D.τ j L.W L.le (sectRes M L.le (D.s i))
  have hγτ : ∀ {W' : Opens Y} (hW' : W' ≤ L.W) (i : Fin D.m),
      Y.res hW' (γ i) = D.τ j W' (hW'.trans L.le) (sectRes M (hW'.trans L.le) (D.s i)) :=
    fun hW' i ↦ by rw [← D.τ_res, sectRes_sectRes]
  have hγ : D.Annihilates L.le γ := fun W' hW' g hg ↦ by
    have := congrArg (D.τ j W' (hW'.trans L.le)) hg
    rw [D.τ_sum_smul, D.τ_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm, hγτ]
  have hτ : Y.res h₁ (D.τ j V (hV.trans L.le) a) = ∑ i, Y.res (h₁.trans hV) (γ i) * f i := by
    rw [← D.τ_res, hfa, D.τ_sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm, hγτ]
  have h0 : ∑ i, Y.res (h₁.trans hV) (γ i) * f i = 0 := by
    refine (L.gen_lam V₁ (h₁.trans hV) _ (hγ.res _)).sum_mul_eq_zero f fun p ↦ ?_
    have := hfv p
    rw [Pi.zero_apply, res_zero] at this
    exact this.symm
  refine ⟨V₁ ⊓ D.U₀, le_inf (inf_le_left.trans h₁) inf_le_right, ⟨hy₁, hy.2⟩, ?_⟩
  rw [res_res, res_res, res_zero]
  refine (Y.res_res inf_le_left h₁ _).symm.trans ?_
  rw [hτ, h0, res_zero]


-- @@ L546-566 verbatim
variable {L hV} in
/-- The values at the `λ_p` of a section annihilate the relations `ρ_l` of the `λ_p`. -/
lemma Rel.sum_mul_ρ {a : M.val.obj (op V)} {v : Fin L.q → Γᵧ(V)} (h : L.Rel hV a v)
    (l : Fin L.q') : ∑ p, v p * Y.res hV (L.ρ l p) = 0 := by
  refine D.injective_res V (hV.trans L.le) (res_eq_of_locally fun y hy ↦ ?_)
  obtain ⟨V₁, h₁, hy₁, f, -, hfv⟩ := h y hy
  have key : Y.res h₁ (∑ p, v p * Y.res hV (L.ρ l p)) = 0 := by
    rw [res_sum]
    calc ∑ p, Y.res h₁ (v p * Y.res hV (L.ρ l p))
        = ∑ p, (∑ i, Y.res (h₁.trans hV) (L.lam p i) * f i) *
            Y.res (h₁.trans hV) (L.ρ l p) :=
          Finset.sum_congr rfl fun p _ ↦ by rw [res_mul, hfv p, res_res]
      _ = ∑ i, f i * Y.res (h₁.trans hV) (∑ p, L.ρ l p * L.lam p i) := by
          simp only [res_sum, res_mul, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦ by ring
      _ = 0 := by simp only [L.rel_ρ, res_zero, mul_zero, Finset.sum_const_zero]
  refine ⟨V₁ ⊓ D.U₀, le_inf (inf_le_left.trans h₁) inf_le_right, ⟨hy₁, hy.2⟩, ?_⟩
  rw [res_res, res_res, res_zero]
  refine (Y.res_res inf_le_left h₁ _).symm.trans ?_
  rw [key, res_zero]


-- @@ L568-650 verbatim
variable {L} in
/-- **Local surjectivity of the evaluation at the `λ_p`**: near every point of `V ∩ U₀`, where `M`
is free with a basis `e_k` in the span of the `sᵢ`, every `v` annihilating the relations `ρ_l`
of the `λ_p` is the value of a section. -/
lemma exists_local_rel {v : Fin L.q → Γᵧ(V)} (hv : ∀ l, ∑ p, v p * Y.res hV (L.ρ l p) = 0)
    {y : Y} (hy : y ∈ V ⊓ D.U₀) : ∃ (V₃ : Opens Y) (h₃ : V₃ ≤ V), y ∈ V₃ ∧
      ∃ a : M.val.obj (op V₃), L.Rel (h₃.trans hV) a (fun p ↦ Y.res h₃ (v p)) := by
  classical
  obtain ⟨Vb, hVbU, r, e, P, hyVb, he, hspan, hindep⟩ := D.exists_basis y hy.2
  -- the expansions `sᵢ = ∑ₖ Q_{ik} eₖ` over `Vb`
  choose Q hQ using fun i ↦ hspan Vb le_rfl (sectRes M hVbU (D.s i))
  have hQ' : ∀ {W' : Opens Y} (h : W' ≤ Vb) (i : Fin D.m),
      sectRes M (h.trans hVbU) (D.s i) = ∑ k, Y.res h (Q i k) • sectRes M h (e k) :=
    fun h i ↦ by
      have := congrArg (sectRes M h) (hQ i)
      simpa only [sectRes_sectRes, sectRes_sum_smul] using this
  -- the coefficient vectors `(Q_{ik})ᵢ` annihilate the relations of the `sᵢ`
  have hann : ∀ k, D.Annihilates hVbU (fun i ↦ Q i k) := fun k W' hW' f hf ↦ by
    have h0 : ∑ k', (∑ i, f i * Y.res hW' (Q i k')) • sectRes M hW' (e k') = 0 := by
      rw [← hf]
      simp only [hQ' hW', Finset.smul_sum, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    rw [← hindep W' hW' _ h0 k]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  -- a common neighbourhood on which they are combinations of the `λ_p`
  have k₂ : Vb ⊓ V ≤ Vb := inf_le_left
  have h₂ : Vb ⊓ V ≤ L.W := inf_le_right.trans hV
  obtain ⟨V₃', hyV₃', hall⟩ := exists_open_forall Y y
    (fun (k : Fin r) (W' : Opens Y) ↦ ∃ (h : W' ≤ Vb ⊓ V) (c : Fin L.q → Γᵧ(W')),
      ∀ i, Y.res (h.trans k₂) (Q i k) = ∑ p, c p * Y.res (h.trans h₂) (L.lam p i))
    (fun k W₁ W₂ h₂₁ ⟨h, c, hc⟩ ↦ ⟨h₂₁.trans h, fun p ↦ Y.res h₂₁ (c p), fun i ↦ by
      have := congrArg (Y.res h₂₁) (hc i)
      simpa only [res_res, res_sum, res_mul] using this⟩)
    fun k ↦ by
      obtain ⟨W₃, h₃, hyW₃, c, hc⟩ := L.gen_lam (Vb ⊓ V) h₂ (fun i ↦ Y.res k₂ (Q i k))
        ((hann k).res k₂) y ⟨hyVb, hy.1⟩
      exact ⟨W₃, hyW₃, h₃, c, fun i ↦ by simpa only [res_res] using hc i⟩
  set V₃ := V₃' ⊓ (Vb ⊓ V)
  have h₃ : V₃ ≤ Vb ⊓ V := inf_le_right
  have hV₃b : V₃ ≤ Vb := h₃.trans k₂
  have hV₃V : V₃ ≤ V := h₃.trans inf_le_right
  choose hk Dc hDc using hall
  set Dc' : Fin r → Fin L.q → Γᵧ(V₃) := fun k p ↦ Y.res inf_le_left (Dc k p)
  have hDc' : ∀ i k, Y.res hV₃b (Q i k) = ∑ p, Dc' k p * Y.res (hV₃V.trans hV) (L.lam p i) :=
    fun i k ↦ by
      have := congrArg (Y.res (inf_le_left : V₃ ≤ V₃')) (hDc k i)
      simpa only [res_res, res_sum, res_mul] using this
  -- the section
  set φ : Fin r → Γᵧ(V₃) := fun k ↦ ∑ p', Dc' k p' * Y.res hV₃V (v p')
  refine ⟨V₃, hV₃V, ⟨hyV₃', hyVb, hy.1⟩, ∑ k, φ k • sectRes M hV₃b (e k), fun y' _ ↦
    ⟨V₃, le_rfl, ‹y' ∈ V₃ ⊓ D.U₀›.1, fun i ↦ ∑ k, φ k * Y.res hV₃b (P k i), ?_, fun p ↦ ?_⟩⟩
  · rw [sectRes_refl]
    simp only [sectRes_sectRes, sectRes_sum_smul, he, Finset.smul_sum, Finset.sum_smul,
      mul_smul]
    exact Finset.sum_comm
  · rw [res_self]
    refine sum_eq_of_relations (fun p i ↦ Y.res (hV₃V.trans hV) (L.lam p i))
      (fun k i ↦ Y.res hV₃b (P k i)) (fun i k ↦ Y.res hV₃b (Q i k)) Dc'
      (fun p ↦ Y.res hV₃V (v p)) hDc' (fun p i ↦ ?_) (fun t ht ↦ ?_) p
    · -- two representations of `sᵢ` over `V₃`
      have h₁ : ∑ i', (∑ k, Y.res hV₃b (Q i k) * Y.res hV₃b (P k i')) •
          sectRes M ((hV₃V.trans hV).trans L.le) (D.s i') =
          ∑ i', (Pi.single i 1 : Fin D.m → Γᵧ(V₃)) i' •
            sectRes M ((hV₃V.trans hV).trans L.le) (D.s i') := by
        have hrhs : ∑ i', (Pi.single i 1 : Fin D.m → Γᵧ(V₃)) i' •
            sectRes M ((hV₃V.trans hV).trans L.le) (D.s i') =
            sectRes M ((hV₃V.trans hV).trans L.le) (D.s i) := by
          rw [Finset.sum_eq_single i (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_smul])
            (by simp), Pi.single_eq_same, one_smul]
        rw [hrhs]
        have := hQ' hV₃b i
        simp only [he, sectRes_sum_smul, sectRes_sectRes, Finset.smul_sum, mul_smul,
          Finset.sum_smul] at this ⊢
        rw [this]
        exact Finset.sum_comm
      have := L.sum_lam_eq (hV₃V.trans hV) h₁ p
      rw [this, Finset.sum_eq_single i (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, mul_zero])
        (by simp), Pi.single_eq_same, mul_one]
    · refine (L.gen_ρ V₃ (hV₃V.trans hV) t ht).sum_mul_eq_zero _ fun l ↦ ?_
      have := congrArg (Y.res hV₃V) (hv l)
      simp only [res_sum, res_mul, res_res, res_zero] at this
      rw [← this]
      exact Finset.sum_congr rfl fun p _ ↦ mul_comm _ _


-- @@ L652-664 verbatim
variable {L hV} in
/-- `Rel` is local on `V ∩ U₀`. -/
lemma rel_of_locally {a : M.val.obj (op V)} {v : Fin L.q → Γᵧ(V)}
    (h : ∀ y ∈ V ⊓ D.U₀, ∃ (V' : Opens Y) (h' : V' ≤ V), y ∈ V' ∧
      L.Rel (h'.trans hV) (sectRes M h' a) (fun p ↦ Y.res h' (v p))) : L.Rel hV a v := by
  intro y hy
  obtain ⟨V', h', hy', hrel⟩ := h y hy
  obtain ⟨V₁, h₁, hy₁, f, hfa, hfv⟩ := hrel y ⟨hy', hy.2⟩
  refine ⟨V₁, h₁.trans h', hy₁, f, ?_, fun p ↦ ?_⟩
  · rw [← sectRes_sectRes M h₁ h']
    exact hfa
  · rw [← res_res Y h₁ h']
    exact hfv p


-- @@ L666-690 verbatim
variable {L} in
/-- **Surjectivity of the evaluation at the `λ_p`** onto the vectors annihilating the relations
`ρ_l` of the `λ_p`: the local preimages glue over `V ∩ U₀` and extend to `V`. -/
lemma exists_rel_of {v : Fin L.q → Γᵧ(V)} (hv : ∀ l, ∑ p, v p * Y.res hV (L.ρ l p) = 0) :
    ∃ a, L.Rel hV a v := by
  choose V₃ h₃ hyV₃ a ha using fun y (hy : y ∈ V ⊓ D.U₀) ↦ L.exists_local_rel hV hv hy
  set O : ∀ y ∈ V ⊓ D.U₀, Opens Y := fun y hy ↦ V₃ y hy ⊓ D.U₀
  have hOV : ∀ y hy, O y hy ≤ V ⊓ D.U₀ := fun y hy ↦ inf_le_inf (h₃ y hy) le_rfl
  have hrelO : ∀ y hy, L.Rel ((hOV y hy).trans (inf_le_left.trans hV))
      (sectRes M inf_le_left (a y hy)) (fun p ↦ Y.res ((hOV y hy).trans inf_le_left) (v p)) :=
    fun y hy ↦ by simpa only [res_res] using (ha y hy).res inf_le_left
  obtain ⟨a₀, ha₀⟩ := exists_sectRes_eq_of_locally M O hOV (fun y hy ↦ ⟨hyV₃ y hy, hy.2⟩)
    (fun y hy ↦ sectRes M inf_le_left (a y hy)) fun y hy z hz ↦ by
      have hW : O y hy ⊓ O z hz ≤ L.W :=
        (inf_le_left.trans (hOV y hy)).trans (inf_le_left.trans hV)
      have h₁ := (hrelO y hy).res (inf_le_left : O y hy ⊓ O z hz ≤ O y hy)
      have h₂ := (hrelO z hz).res (inf_le_right : O y hy ⊓ O z hz ≤ O z hz)
      have h₀ := h₁.sub h₂
      simp only [res_res, sub_self] at h₀
      exact sub_eq_zero.1 (Rel.eq_zero (by simpa only [Pi.sub_def, sub_self] using h₀))
  obtain ⟨a', ha'⟩ := D.surjective_sectRes V (hV.trans L.le) a₀
  refine ⟨a', rel_of_locally fun y hy ↦ ⟨O y hy, (hOV y hy).trans inf_le_left,
    ⟨hyV₃ y hy, hy.2⟩, ?_⟩⟩
  rw [← sectRes_sectRes M (hOV y hy) inf_le_left, ha', ha₀ y hy]
  exact hrelO y hy


-- @@ L692-712 verbatim
/-- **Local generators of `M`**: the preimages of the generators `ε_l` of the vectors
annihilating the `ρ_l` generate `M` over `W`. -/
theorem exists_generators : ∃ (k : ℕ) (t : Fin k → M.val.obj (op L.W)),
    ∀ (W' : Opens Y) (hW' : W' ≤ L.W) (a : M.val.obj (op W')), ∀ y ∈ W',
      ∃ (W'' : Opens Y) (hW'' : W'' ≤ W'), y ∈ W'' ∧ ∃ c : Fin k → Γᵧ(W''),
        sectRes M hW'' a = ∑ l, c l • sectRes M (hW''.trans hW') (t l) := by
  choose t ht using fun l ↦ L.exists_rel_of le_rfl (v := L.ε l) fun l' ↦ by
    simpa only [res_self] using L.rel_ε l l'
  refine ⟨L.q'', t, fun W' hW' a y hy ↦ ?_⟩
  obtain ⟨v, hv⟩ := L.exists_rel hW' a
  obtain ⟨W'', hW'', hy'', c, hc⟩ := L.gen_ε W' hW' v hv.sum_mul_ρ y hy
  refine ⟨W'', hW'', hy'', c, ?_⟩
  have h₁ := hv.res hW''
  have h₂ := L.rel_sum (hW''.trans hW') Finset.univ c
    (fun l ↦ sectRes M (hW''.trans hW') (t l)) (fun l p ↦ Y.res (hW''.trans hW') (L.ε l p))
    fun l _ ↦ by simpa only using (ht l).res (hW''.trans hW')
  have h₀ := h₁.sub h₂
  have hv0 : ((fun p ↦ Y.res hW'' (v p)) - fun p ↦ ∑ l, c l * Y.res (hW''.trans hW') (L.ε l p)) =
      0 := funext fun p ↦ by rw [Pi.sub_apply, hc p, sub_self, Pi.zero_apply]
  rw [hv0] at h₀
  exact sub_eq_zero.1 h₀.eq_zero


-- @@ L714-714 verbatim
end LocalData


-- @@ L716-731 verbatim
include D in
/-- Relations of sections of `M` over any open containing a point of `U` are locally finitely
generated near that point. -/
theorem exists_relations_of_mem (hO : HasLocalTupleRelations (SheafOfModules.unit Y.ringSheaf))
    {V : Opens Y} {k : ℕ} (f : Fin k → M.val.obj (op V)) {x : Y} (hxV : x ∈ V) (hxU : x ∈ U) :
    ∃ (W : Opens Y) (hWV : W ≤ V) (q : ℕ) (g : Fin q → Fin k → Γᵧ(W)),
      x ∈ W ∧ (∀ l, ∑ i, g l i • sectRes M hWV (f i) = 0) ∧
      ∀ (W' : Opens Y) (hW' : W' ≤ W) (a : Fin k → Γᵧ(W')),
        (∑ i, a i • sectRes M (hW'.trans hWV) (f i) = 0) → ∀ y ∈ W',
          ∃ (W'' : Opens Y) (hW'' : W'' ≤ W'), y ∈ W'' ∧ ∃ c : Fin q → Γᵧ(W''),
            ∀ i, Y.res hW'' (a i) = ∑ l, c l * Y.res (hW''.trans hW') (g l i) := by
  obtain ⟨W, hW, q, g, hxW, hg, hgen⟩ := D.exists_relations hO (inf_le_right : V ⊓ U ≤ U)
    (fun i ↦ sectRes M inf_le_left (f i)) ⟨hxV, hxU⟩
  refine ⟨W, hW.trans inf_le_left, q, g, hxW, fun l ↦ ?_, fun W' hW' a ha ↦ hgen W' hW' a ?_⟩
  · simpa only [sectRes_sectRes] using hg l
  · simpa only [sectRes_sectRes] using ha


-- @@ L733-733 verbatim
end ReflexiveHullData


-- @@ L735-748 verbatim
/-- **The reflexive hull criterion for coherence.** Let `M` be a sheaf of `𝒪_Y`-modules on a
locally ringed space whose structure sheaf has locally finitely generated tuple relations (e.g. a
complex analytic space). If every point has a neighbourhood `U` carrying the data
`ReflexiveHullData M U`, then `M` is coherent. -/
theorem isCoherent_of_reflexiveHullData
    (hO : HasLocalTupleRelations (SheafOfModules.unit Y.ringSheaf))
    (M : SheafOfModules.{u} Y.ringSheaf)
    (h : ∀ x : Y, ∃ U : Opens Y, x ∈ U ∧ Nonempty (ReflexiveHullData M U)) : M.IsCoherent := by
  choose U hxU D using h
  refine isCoherent_of_hasLocalModuleRelations M (fun x ↦ ?_) fun V k f x hx ↦
    ReflexiveHullData.exists_relations_of_mem (D x).some hO f hx (hxU x)
  obtain ⟨L⟩ := (D x).some.nonempty_localData hO (hxU x)
  obtain ⟨k, t, ht⟩ := L.exists_generators
  exact ⟨L.W, k, t, L.mem, ht⟩


-- @@ L750-750 verbatim
end AlgebraicGeometry.LocallyRingedSpace
