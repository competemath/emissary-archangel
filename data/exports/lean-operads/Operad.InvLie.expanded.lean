/-
# The graded Lie algebra of invariant families, and twisted differentials

The graded commutator of the product of invariant families of a graded operad,

  `[q, q'] = q ⋆ q' - σ(|q| |q'|) q' ⋆ q`,

is a **graded Lie bracket** (`GrOperad.Inv.bracket`), defined on all invariant families through
their parity decompositions (`GrOperad.Inv.parI`). For the convolution operad of a cooperad and
an operad, it is the bracket of the convolution Lie algebra.

* The bracket adds parities (`GrOperad.Inv.isPar_bracket`), is **graded antisymmetric**
  (`GrOperad.Inv.bracket_swap`) and satisfies **the graded Jacobi identity**
  (`GrOperad.Inv.jacobi`), by the graded pre-Lie identity.
* Morphisms of graded operads preserve the bracket (`GrOperad.Inv.appHom_bracket`), and
  derivations are derivations of the bracket (`GrOperad.Inv.appDer_bracket`).
* For an odd family `α`, `[α, α] = 2 α ⋆ α` (`GrOperad.Inv.bracket_self_odd`), and
  `[α, [α, x]] = [α ⋆ α, x]` (`GrOperad.Inv.bracket_bracket_odd`), without dividing by two.
* **Twisted differentials** (`GrOperad.Inv.twD_twD`): for an odd derivation `D` squaring to zero
  and an odd family `α` with `D α + α ⋆ α = 0`, the twisted differential `D_α = D + [α, -]` is
  odd and squares to zero. For a twisting morphism `α : C → P`, this is **the twisted convolution
  complex** (`Operad.Twisting.twD_twD`); when `2` is invertible, the Maurer–Cartan equation reads
  `∂α + ½ [α, α] = 0` (`Operad.Twisting.mc_bracket`).
-/
import Operad.Twisting


-- @@ L27-30 verbatim
universe u v w

/- The input types of nested composites are nested sums of subtypes, whose instances grow with the
nesting depth. -/

-- @@ L31-31 verbatim
set_option synthInstance.maxSize 2048


-- @@ L33-33 verbatim
namespace Operad


-- @@ L35-35 verbatim
open Sym GerBV


-- @@ L37-37 verbatim
namespace GrOperad


-- @@ L39-41 verbatim
variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [GrOperad R Q]


-- @@ L43-43 verbatim
namespace Inv


-- @@ L45-45 verbatim
/-! ## Parities of invariant families -/


-- @@ L47-55 verbatim
/-- The parity projections of invariant families, arity by arity. -/
def parI (b : Bool) : Inv R Q →ₗ[R] Inv R Q where
  toFun q := ⟨fun A _ _ => par (R := R) b (q.1 A), fun A B _ _ _ _ e => by
    show map (R := R) e (par (R := R) b (q.1 A)) = par (R := R) b (q.1 B)
    rw [map_par, map_apply]⟩
  map_add' q q' := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_add (par (R := R) b) _ _)
  map_smul' c q := Subtype.ext (funext fun A => funext fun _ => funext fun _ =>
    map_smul (par (R := R) b) _ _)


-- @@ L57-58 verbatim
@[simp] lemma parI_apply (b : Bool) (q : Inv R Q) (A : Type) [Fintype A] [DecidableEq A] :
    (parI b q).1 A = par (R := R) b (q.1 A) := rfl


-- @@ L60-62 verbatim
lemma isPar_parI (b : Bool) (q : Inv R Q) : IsPar b (parI b q) := fun A _ _ => by
  show par (R := R) b (par (R := R) b (q.1 A)) = par (R := R) b (q.1 A)
  rw [par_par, if_pos rfl]


-- @@ L64-66 verbatim
/-- Every invariant family is the sum of its even and odd parts. -/
lemma parI_add (q : Inv R Q) : parI false q + parI true q = q :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => par_add (R := R) (q.1 A))


-- @@ L68-78 verbatim
/-- The parity projections of a homogeneous family. -/
lemma parI_eq {b : Bool} {q : Inv R Q} (hq : IsPar b q) (c : Bool) :
    parI c q = if c = b then q else 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ?_)
  show par (R := R) c (q.1 A) = (if c = b then q else 0 : Inv R Q).1 A
  by_cases h : c = b
  · subst h
    rw [if_pos rfl]
    exact hq A
  · rw [if_neg h, ← hq A, par_par, if_neg h]
    rfl


-- @@ L80-83 verbatim
lemma IsPar.add {b : Bool} {q q' : Inv R Q} (hq : IsPar b q) (hq' : IsPar b q') :
    IsPar b (q + q') := fun A _ _ => by
  show par (R := R) b (q.1 A + q'.1 A) = q.1 A + q'.1 A
  rw [map_add, hq A, hq' A]


-- @@ L85-88 verbatim
lemma IsPar.sub {b : Bool} {q q' : Inv R Q} (hq : IsPar b q) (hq' : IsPar b q') :
    IsPar b (q - q') := fun A _ _ => by
  show par (R := R) b (q.1 A - q'.1 A) = q.1 A - q'.1 A
  rw [map_sub, hq A, hq' A]


-- @@ L90-93 verbatim
lemma IsPar.smul {b : Bool} {q : Inv R Q} (c : R) (hq : IsPar b q) : IsPar b (c • q) :=
  fun A _ _ => by
    show par (R := R) b (c • q.1 A) = c • q.1 A
    rw [map_smul, hq A]


-- @@ L95-97 verbatim
lemma isPar_zero (b : Bool) : IsPar b (0 : Inv R Q) := fun A _ _ => by
  show par (R := R) b 0 = 0
  rw [map_zero]


-- @@ L99-99 verbatim
/-! ## The bracket -/


-- @@ L101-118 verbatim
variable (R Q) in
/-- **The graded commutator** of invariant families, `[q, q'] = q ⋆ q' - σ(|q| |q'|) q' ⋆ q`,
through their parity decompositions. -/
def bracket : Inv R Q →ₗ[R] Inv R Q →ₗ[R] Inv R Q :=
  LinearMap.mk₂ R (fun q q' => star R Q q q'
      - ∑ b : Bool, ∑ b' : Bool, σ R (b && b') • star R Q (parI b' q') (parI b q))
    (fun q₁ q₂ q' => by
      simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]
      abel)
    (fun c q q' => by
      simp only [map_smul, LinearMap.smul_apply, smul_comm (σ R _) c, ← Finset.smul_sum,
        smul_sub])
    (fun q q'₁ q'₂ => by
      simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]
      abel)
    (fun c q q' => by
      simp only [map_smul, LinearMap.smul_apply, smul_comm (σ R _) c, ← Finset.smul_sum,
        smul_sub])


-- @@ L120-122 verbatim
lemma bracket_apply (q q' : Inv R Q) :
    bracket R Q q q' = star R Q q q'
      - ∑ b : Bool, ∑ b' : Bool, σ R (b && b') • star R Q (parI b' q') (parI b q) := rfl


-- @@ L124-129 verbatim
/-- **The bracket of homogeneous families.** -/
theorem bracket_hom {p p' : Bool} {q q' : Inv R Q} (hq : IsPar p q) (hq' : IsPar p' q') :
    bracket R Q q q' = star R Q q q' - σ R (p && p') • star R Q q' q := by
  rw [bracket_apply, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [parI_eq hq, parI_eq hq']
  cases p <;> cases p' <;> simp


-- @@ L131-135 verbatim
/-- **The bracket adds parities.** -/
theorem isPar_bracket {p p' : Bool} {q q' : Inv R Q} (hq : IsPar p q) (hq' : IsPar p' q') :
    IsPar (xor p p') (bracket R Q q q') := by
  rw [bracket_hom hq hq']
  refine (isPar_star hq hq').sub ((Bool.xor_comm p' p) ▸ (isPar_star hq' hq).smul _)


-- @@ L137-142 verbatim
/-- **Graded antisymmetry.** -/
theorem bracket_swap {p p' : Bool} {q q' : Inv R Q} (hq : IsPar p q) (hq' : IsPar p' q') :
    bracket R Q q q' = -(σ R (p && p') • bracket R Q q' q) := by
  rw [bracket_hom hq hq', bracket_hom hq' hq, Bool.and_comm p' p, smul_sub, smul_smul,
    σ_mul_self, one_smul]
  abel


-- @@ L144-161 verbatim
/-- **The graded Jacobi identity.** -/
theorem jacobi {p p' p'' : Bool} {q q' q'' : Inv R Q} (hq : IsPar p q) (hq' : IsPar p' q')
    (hq'' : IsPar p'' q'') :
    σ R (p && p'') • bracket R Q q (bracket R Q q' q'')
      + σ R (p' && p) • bracket R Q q' (bracket R Q q'' q)
      + σ R (p'' && p') • bracket R Q q'' (bracket R Q q q') = 0 := by
  rw [bracket_hom hq (isPar_bracket hq' hq''), bracket_hom hq' (isPar_bracket hq'' hq),
    bracket_hom hq'' (isPar_bracket hq hq'), bracket_hom hq' hq'', bracket_hom hq'' hq,
    bracket_hom hq hq']
  have h1 := preLie q q' q'' hq' hq''
  have h2 := preLie q' q'' q hq'' hq
  have h3 := preLie q'' q q' hq hq'
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2 h3 ⊢
  linear_combination (norm := skip)
    (-σ R (p && p'')) • h1 - σ R (p' && p) • h2 - σ R (p'' && p') • h3
  cases p <;> cases p' <;> cases p'' <;>
    simp only [Bool.and_true, Bool.and_false, Bool.xor_true, Bool.xor_false, Bool.not_true,
      Bool.not_false, σ_true, σ_false] <;> module


-- @@ L163-163 verbatim
/-! ## Morphisms and derivations -/


-- @@ L165-167 verbatim
variable {Q' : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q' A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q' A)] [GrOperad R Q']


-- @@ L169-171 verbatim
lemma appHom_parI (φ : GrOperadHom R Q Q') (b : Bool) (q : Inv R Q) :
    appHom φ (parI b q) = parI b (appHom φ q) :=
  Subtype.ext (funext fun A => funext fun _ => funext fun _ => φ.app_par b (q.1 A))


-- @@ L173-176 verbatim
/-- **Morphisms of graded operads preserve the bracket.** -/
theorem appHom_bracket (φ : GrOperadHom R Q Q') (q q' : Inv R Q) :
    appHom φ (bracket R Q q q') = bracket R Q' (appHom φ q) (appHom φ q') := by
  simp only [bracket_apply, map_sub, map_sum, map_smul, appHom_star, appHom_parI]


-- @@ L178-188 verbatim
/-- **Derivations are derivations of the bracket**, with the Koszul sign of the left factor. -/
theorem appDer_bracket {e p p' : Bool} (D : GrDer (GrOperadHom.id R Q) e) {q q' : Inv R Q}
    (hq : IsPar p q) (hq' : IsPar p' q') :
    appDer D (bracket R Q q q')
      = bracket R Q (appDer D q) q' + σ R (e && p) • bracket R Q q (appDer D q') := by
  rw [bracket_hom hq hq', bracket_hom (isPar_appDer D hq) hq',
    bracket_hom hq (isPar_appDer D hq'), map_sub, map_smul, appDer_star D hq,
    appDer_star D hq']
  cases e <;> cases p <;> cases p' <;>
    simp only [Bool.and_true, Bool.and_false, Bool.xor_true, Bool.xor_false, Bool.not_true,
      Bool.not_false, σ_true, σ_false] <;> module


-- @@ L190-190 verbatim
/-! ## Odd families -/


-- @@ L192-195 verbatim
/-- **The bracket of an odd family with itself is twice its square.** -/
theorem bracket_self_odd {α : Inv R Q} (hα : IsPar true α) :
    bracket R Q α α = (2 : R) • star R Q α α := by
  rw [bracket_hom hα hα, Bool.and_self, σ_true, neg_one_smul_inv, sub_neg_eq_add, two_smul]


-- @@ L197-211 verbatim
/-- **The bracket with an odd family twice is the bracket with its square**:
`[α, [α, x]] = [α ⋆ α, x]`, by the graded pre-Lie identity and the vanishing of the associator
of `α` with itself. -/
theorem bracket_bracket_odd {α : Inv R Q} (hα : IsPar true α) {p : Bool} {x : Inv R Q}
    (hx : IsPar p x) :
    bracket R Q α (bracket R Q α x) = bracket R Q (star R Q α α) x := by
  rw [bracket_hom hα (isPar_bracket hα hx), bracket_hom hα hx,
    bracket_hom (isPar_star hα hα) hx]
  have h1 := preLie α α x hα hx
  have h2 := assoc_odd x α hα
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply] at h1 ⊢
  linear_combination (norm := skip) -h1 - h2
  cases p <;>
    simp only [Bool.and_true, Bool.and_false, Bool.xor_true, Bool.xor_false, Bool.not_true,
      σ_true, σ_false] <;> module


-- @@ L213-213 verbatim
/-! ## Twisted differentials -/


-- @@ L215-217 verbatim
/-- **The twisted differential** `D_α = D + [α, -]`. -/
def twD (D : GrDer (GrOperadHom.id R Q) true) (α : Inv R Q) : Inv R Q →ₗ[R] Inv R Q :=
  appDer D + bracket R Q α


-- @@ L219-220 verbatim
lemma twD_apply (D : GrDer (GrOperadHom.id R Q) true) (α x : Inv R Q) :
    twD D α x = appDer D x + bracket R Q α x := rfl


-- @@ L222-230 verbatim
/-- **The twisted differential of an odd family is odd.** -/
theorem isPar_twD (D : GrDer (GrOperadHom.id R Q) true) {α : Inv R Q} (hα : IsPar true α)
    {p : Bool} {x : Inv R Q} (hx : IsPar p x) : IsPar (!p) (twD D α x) := by
  rw [twD_apply]
  have h1 := isPar_appDer D hx
  have h2 := isPar_bracket hα hx
  rw [Bool.xor_true] at h1
  rw [Bool.true_xor] at h2
  exact h1.add h2


-- @@ L232-241 verbatim
/-- **The twisted differential squares to zero** on homogeneous families. -/
theorem twD_twD_hom (D : GrDer (GrOperadHom.id R Q) true)
    (hD : ∀ x : Inv R Q, appDer D (appDer D x) = 0) {α : Inv R Q} (hα : IsPar true α)
    (hmc : appDer D α + star R Q α α = 0) {p : Bool} {x : Inv R Q} (hx : IsPar p x) :
    twD D α (twD D α x) = 0 := by
  have h : bracket R Q (appDer D α) x + bracket R Q (star R Q α α) x = 0 := by
    rw [← LinearMap.add_apply, ← map_add, hmc, map_zero, LinearMap.zero_apply]
  rw [twD_apply, twD_apply, map_add, map_add, hD, appDer_bracket D hα hx,
    bracket_bracket_odd hα hx, Bool.and_self, σ_true, neg_one_smul_inv]
  linear_combination (norm := module) h


-- @@ L243-248 verbatim
/-- **The twisted differential squares to zero.** -/
theorem twD_twD (D : GrDer (GrOperadHom.id R Q) true)
    (hD : ∀ x : Inv R Q, appDer D (appDer D x) = 0) {α : Inv R Q} (hα : IsPar true α)
    (hmc : appDer D α + star R Q α α = 0) (x : Inv R Q) : twD D α (twD D α x) = 0 := by
  rw [← parI_add x, map_add, map_add, twD_twD_hom D hD hα hmc (isPar_parI false x),
    twD_twD_hom D hD hα hmc (isPar_parI true x), add_zero]


-- @@ L250-250 verbatim
end Inv


-- @@ L252-252 verbatim
end GrOperad


-- @@ L254-254 verbatim
/-! ## The twisted convolution complex of a twisting morphism -/


-- @@ L256-256 verbatim
namespace Twisting


-- @@ L258-264 verbatim
variable {R : Type u} [CommRing R] {C : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (C A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (C A)] [GrCooperad R C]
  [GrCooperad.Coaug R C]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]


-- @@ L266-269 verbatim
variable (R C P) in
/-- The differential of the convolution operad: composition with the differential of `P`. -/
noncomputable abbrev convD : GrDer (GrOperadHom.id R (ConvOp R C P)) true :=
  ConvOp.postDer (C := C) (DGOperad.toDer (R := R) (P := P))


-- @@ L271-277 verbatim
omit [GrCooperad.Coaug R C] in
/-- The differential of the convolution operad squares to zero. -/
lemma convD_convD (x : GrOperad.Inv R (ConvOp R C P)) :
    GrOperad.Inv.appDer (convD R C P) (GrOperad.Inv.appDer (convD R C P) x) = 0 := by
  refine Subtype.ext (funext fun A => funext fun _ => funext fun _ => ConvOp.ext fun y => ?_)
  rw [ConvOp.appDer_postDer_apply, ConvOp.appDer_postDer_apply]
  exact DGOperad.d_d _


-- @@ L279-283 verbatim
/-- **The twisted convolution complex** of a twisting morphism: the twisted differential
`∂ + [α, -]` squares to zero. -/
theorem twD_twD (α : Twisting R C P) (x : GrOperad.Inv R (ConvOp R C P)) :
    GrOperad.Inv.twD (convD R C P) α.1 (GrOperad.Inv.twD (convD R C P) α.1 x) = 0 :=
  GrOperad.Inv.twD_twD _ convD_convD α.2.1 α.2.2.2 x


-- @@ L285-293 verbatim
omit [GrCooperad.Coaug R C] in
/-- **The Maurer–Cartan equation in bracket form**: when `2` is invertible, an odd family `α`
satisfies `∂α + α ⋆ α = 0` exactly when `∂α + ½ [α, α] = 0`. -/
theorem mc_bracket [Invertible (2 : R)] {α : GrOperad.Inv R (ConvOp R C P)}
    (hα : GrOperad.Inv.IsPar true α) :
    GrOperad.Inv.appDer (convD R C P) α + GrOperad.Inv.star R _ α α = 0
      ↔ GrOperad.Inv.appDer (convD R C P) α
          + ⅟(2 : R) • GrOperad.Inv.bracket R _ α α = 0 := by
  rw [GrOperad.Inv.bracket_self_odd hα, smul_smul, invOf_mul_self, one_smul]


-- @@ L295-295 verbatim
end Twisting


-- @@ L297-297 verbatim
end Operad
