import StringDiagrams.Super.QPiTwoHom
import StringDiagrams.Super.GSKar
import StringDiagrams.Super.KarBicategory
import Mathlib.Algebra.DirectSum.Module


-- @@ L6-36 verbatim
/-!
# The Grothendieck ring of an additive 2-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the end of
§6 (and J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133, (1.32)).

For a bicategory `B` whose hom categories are additive (preadditive with binary biproducts) and
whose whiskerings are additive, the *Grothendieck ring* is

  `K₀Ring B := ⨁_{(λ, μ)} K₀ (λ ⟶ μ)`,
the direct sum of the split Grothendieck groups of the hom categories, with the multiplication
induced by horizontal composition: for `F : λ → μ` and `G : μ → ν`, `[G] · [F] = [F ≫ G]`
(the composite `λ → ν`; classes of non-composable 1-morphisms multiply to zero). It is a
(non-unital, associative) ring (`K₀Ring.instNonUnitalRing`) with the distinguished mutually
orthogonal idempotents `1_λ := [𝟙 λ]` (`K₀Ring.one`, `K₀Ring.one_mul_one_self`,
`K₀Ring.one_mul_one_of_ne`); it is *locally unital*: `1_μ · x = x = x · 1_λ` for
`x ∈ K₀ (λ ⟶ μ)` (`K₀Ring.one_mul_of`, `K₀Ring.of_mul_one`), and every element is fixed by
left and right multiplication by a finite sum of the `1_λ` (`K₀Ring.exists_finset_one_mul`).

For a `(Q, Π)`-2-category (Definition 6.14) `K₀Ring B` is a `Zπ[q, q⁻¹]`-module
(`K₀Ring.moduleLaurent`, componentwise via `K₀.moduleLaurent` of the hom `(Q, Π)`-categories),
`π` and `q` acting on `1_μ K₀ 1_λ = K₀ (λ ⟶ μ)` by left multiplication by `[π_μ]` and `[q_μ]`
(`K₀Ring.C_π_smul_of`, `K₀Ring.T_smul_of`), equivalently by right multiplication by `[π_λ]` and
`[q_λ]` (`K₀Ring.C_π_smul_of'`, `K₀Ring.T_smul_of'`; the equivalence uses the isomorphisms
`β_F : F π_μ ≅ π_λ F` and `γ_F : F q_μ ≅ q_λ F`); the module structure is compatible with the
multiplication (`K₀Ring.smul_mul`, `K₀Ring.mul_smul`), so `K₀Ring B` is a locally unital
`Zπ[q, q⁻¹]`-algebra. Applied to `GSKAR(𝔄)` (`StringDiagrams.Super.KarBicategory`) this is the
Grothendieck ring `K₀(GSKAR(𝔄))` at the end of §6.

Compositions of 1-morphisms are written in diagrammatic order (`F ≫ G` is the paper's `GF`).
-/


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace StringDiagrams


-- @@ L42-42 verbatim
open CategoryTheory Bicategory Limits


-- @@ L44-44 verbatim
universe w v u w₁


-- @@ L46-46 verbatim
section Ring


-- @@ L48-49 verbatim
variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]


-- @@ L51-51 verbatim
/-! ## Horizontal composition on `K₀` -/


-- @@ L53-53 verbatim
namespace K₀


-- @@ L55-59 verbatim
/-- The natural isomorphism `precomp c f ≅ precomp c f'` induced by `f ≅ f'`. -/
@[simps!]
def precompIso {a b c : B} {f f' : a ⟶ b} (e : f ≅ f') : precomp c f ≅ precomp c f' :=
  NatIso.ofComponents (fun g => whiskerRightIso e g) fun η => by
    exact whisker_exchange _ _


-- @@ L61-61 verbatim
variable (a b c : B)


-- @@ L63-70 verbatim
/-- **Horizontal composition on `K₀`**: the bilinear map `K₀ (a ⟶ b) →+ K₀ (b ⟶ c) →+ K₀ (a ⟶ c)`
with `[f] · [g] = [f ≫ g]`. -/
def hcompK : K₀ (a ⟶ b) →+ K₀ (b ⟶ c) →+ K₀ (a ⟶ c) :=
  lift (fun f => map (precomp c f)) (fun _ _ e => map_eq_of_iso (precompIso e)) fun f f' =>
    hom_ext fun g => by
      simp only [map_mk, AddMonoidHom.add_apply]
      change mk ((postcomp a g).obj (f ⊞ f')) = mk ((postcomp a g).obj f) + mk ((postcomp a g).obj f')
      rw [mk_eq_mk_of_iso (mapBiprodIso (postcomp a g) f f'), mk_biprod]


-- @@ L72-72 verbatim
variable {a b c}


-- @@ L74-75 verbatim
@[simp] theorem hcompK_mk_mk (f : a ⟶ b) (g : b ⟶ c) : hcompK a b c (mk f) (mk g) = mk (f ≫ g) := by
  simp [hcompK]


-- @@ L77-77 verbatim
end K₀


-- @@ L79-79 verbatim
/-! ## The Grothendieck ring -/


-- @@ L81-84 verbatim
variable (B) in
/-- **Brundan–Ellis, end of §6; Super Kac–Moody 2-categories (1.32).** The Grothendieck ring
`K₀(B) := ⨁_{(λ, μ)} K₀ (λ ⟶ μ)` of an additive 2-category. -/
abbrev K₀Ring := DirectSum (B × B) fun p => K₀ (p.1 ⟶ p.2)


-- @@ L86-86 verbatim
namespace K₀Ring


-- @@ L88-88 verbatim
open scoped Classical


-- @@ L90-90 verbatim
variable (a b : B)


-- @@ L92-93 verbatim
/-- The inclusion of `K₀ (a ⟶ b)`, the summand `1_b K₀ 1_a`. -/
def of : K₀ (a ⟶ b) →+ K₀Ring B := DirectSum.of (fun p : B × B => K₀ (p.1 ⟶ p.2)) (a, b)


-- @@ L95-96 verbatim
omit [PreadditiveBicategory B] in
theorem of_injective : Function.Injective (of a b) := DirectSum.of_injective (a, b)


-- @@ L98-98 verbatim
variable {a b}


-- @@ L100-101 verbatim
/-- The class `[f]` of a 1-morphism. -/
def mk (f : a ⟶ b) : K₀Ring B := of a b (K₀.mk f)


-- @@ L103-105 verbatim
omit [PreadditiveBicategory B] in
theorem mk_eq_mk_of_iso {f f' : a ⟶ b} (e : f ≅ f') : mk f = mk f' := by
  rw [mk, mk, K₀.mk_eq_mk_of_iso e]


-- @@ L107-109 verbatim
omit [PreadditiveBicategory B] in
theorem mk_biprod (f f' : a ⟶ b) : mk (f ⊞ f') = mk f + mk f' := by
  rw [mk, mk, mk, K₀.mk_biprod, map_add]


-- @@ L111-115 verbatim
omit [PreadditiveBicategory B] in
/-- Additive homomorphisms out of `K₀Ring B` are determined by their values on the summands. -/
theorem addHom_ext {G : Type w₁} [AddCommGroup G] {φ ψ : K₀Ring B →+ G}
    (h : ∀ (a b : B) (x : K₀ (a ⟶ b)), φ (of a b x) = ψ (of a b x)) : φ = ψ :=
  DirectSum.addHom_ext fun p x => h p.1 p.2 x


-- @@ L117-123 verbatim
omit [PreadditiveBicategory B] in
/-- Induction on elements of `K₀Ring B`. -/
@[elab_as_elim]
theorem induction_on {P : K₀Ring B → Prop} (x : K₀Ring B) (zero : P 0)
    (of : ∀ (a b : B) (x : K₀ (a ⟶ b)), P (of a b x)) (add : ∀ x y, P x → P y → P (x + y)) :
    P x :=
  DirectSum.induction_on x zero (fun p x => of p.1 p.2 x) add


-- @@ L125-125 verbatim
/-! ### The multiplication -/


-- @@ L127-129 verbatim
/-- Transport of `K₀ (c ⟶ d)` along an equality of objects `d = a`. -/
def castHom {c d a : B} (h : d = a) : K₀ (c ⟶ d) →+ K₀ (c ⟶ a) := by
  subst h; exact AddMonoidHom.id _


-- @@ L131-132 verbatim
omit [PreadditiveBicategory B] in
theorem castHom_rfl (c d : B) : castHom (c := c) (rfl : d = d) = AddMonoidHom.id _ := rfl


-- @@ L134-140 verbatim
variable (B) in
/-- The product of the summands `K₀ (p.1 ⟶ p.2)` and `K₀ (q.1 ⟶ q.2)`: zero unless
`q.2 = p.1`, and then `[f] · [g] = [g ≫ f]`. -/
def mulOf (p q : B × B) : K₀ (p.1 ⟶ p.2) →+ K₀ (q.1 ⟶ q.2) →+ K₀Ring B :=
  if h : q.2 = p.1 then
    ((K₀.hcompK q.1 p.1 p.2).flip.compl₂ (castHom h)).compr₂ (of q.1 p.2)
  else 0


-- @@ L142-145 verbatim
theorem mulOf_of_ne {a b c d : B} (h : d ≠ a) (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ d)) :
    mulOf B (a, b) (c, d) x y = 0 := by
  rw [mulOf, dite_eq_right h]
  rfl


-- @@ L147-150 verbatim
theorem mulOf_self (a b c : B) (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ a)) :
    mulOf B (a, b) (c, a) x y = of c b (K₀.hcompK c a b y x) := by
  rw [mulOf, dite_eq_left rfl]
  rfl


-- @@ L152-155 verbatim
variable (B) in
/-- The multiplication of `K₀Ring B`, as a bilinear map. -/
def mulHom : K₀Ring B →+ K₀Ring B →+ K₀Ring B :=
  DirectSum.toAddMonoid fun p => (DirectSum.toAddMonoid fun q => (mulOf B p q).flip).flip


-- @@ L157-157 verbatim
instance : Mul (K₀Ring B) := ⟨fun x y => mulHom B x y⟩


-- @@ L159-159 verbatim
theorem mul_def (x y : K₀Ring B) : x * y = mulHom B x y := rfl


-- @@ L161-164 verbatim
theorem of_mul_of {a b c d : B} (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ d)) :
    of a b x * of c d y = mulOf B (a, b) (c, d) x y := by
  rw [mul_def, mulHom, of, of, DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply,
    DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply]


-- @@ L166-169 verbatim
/-- `[f] · [g] = [g ≫ f]` for `g : c → a`, `f : a → b`. -/
theorem mk_mul_mk (f : a ⟶ b) {c : B} (g : c ⟶ a) : mk f * mk g = mk (g ≫ f) := by
  rw [mk, mk, of_mul_of, mulOf_self, K₀.hcompK_mk_mk]
  rfl


-- @@ L171-173 verbatim
/-- Classes of non-composable 1-morphisms multiply to zero. -/
theorem mk_mul_mk_of_ne (f : a ⟶ b) {c d : B} (g : c ⟶ d) (h : d ≠ a) : mk f * mk g = 0 := by
  rw [mk, mk, of_mul_of, mulOf_of_ne h]


-- @@ L175-176 verbatim
protected theorem mul_add (x y z : K₀Ring B) : x * (y + z) = x * y + x * z :=
  map_add (mulHom B x) y z


-- @@ L178-179 verbatim
protected theorem add_mul (x y z : K₀Ring B) : (x + y) * z = x * z + y * z := by
  simp only [mul_def, map_add, AddMonoidHom.add_apply]


-- @@ L181-181 verbatim
protected theorem mul_zero (x : K₀Ring B) : x * 0 = 0 := map_zero (mulHom B x)


-- @@ L183-184 verbatim
protected theorem zero_mul (x : K₀Ring B) : 0 * x = 0 := by
  simp only [mul_def, map_zero, AddMonoidHom.zero_apply]


-- @@ L186-186 verbatim
protected theorem mul_neg (x y : K₀Ring B) : x * -y = -(x * y) := map_neg (mulHom B x) y


-- @@ L188-189 verbatim
protected theorem neg_mul (x y : K₀Ring B) : -x * y = -(x * y) := by
  simp only [mul_def, map_neg, AddMonoidHom.neg_apply]


-- @@ L191-205 verbatim
theorem mul_assoc_mk {a b c d e e' : B} (f : a ⟶ b) (g : c ⟶ d) (h : e ⟶ e') :
    mk f * mk g * mk h = mk f * (mk g * mk h) := by
  by_cases h1 : d = a
  · subst h1
    rw [mk_mul_mk]
    by_cases h2 : e' = c
    · subst h2
      rw [mk_mul_mk, mk_mul_mk, mk_mul_mk]
      exact mk_eq_mk_of_iso (α_ h g f).symm
    · rw [mk_mul_mk_of_ne _ _ h2, mk_mul_mk_of_ne _ _ h2, K₀Ring.mul_zero]
  · rw [mk_mul_mk_of_ne _ _ h1, K₀Ring.zero_mul]
    by_cases h2 : e' = c
    · subst h2
      rw [mk_mul_mk, mk_mul_mk_of_ne _ _ h1]
    · rw [mk_mul_mk_of_ne _ _ h2, K₀Ring.mul_zero]


-- @@ L207-223 verbatim
theorem mul_assoc_of {a b c d e e' : B} (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ d)) (z : K₀ (e ⟶ e')) :
    of a b x * of c d y * of e e' z = of a b x * (of c d y * of e e' z) := by
  induction x using K₀.induction_on with
  | mk f =>
    induction y using K₀.induction_on with
    | mk g =>
      induction z using K₀.induction_on with
      | mk h => exact mul_assoc_mk f g h
      | zero => simp only [map_zero, K₀Ring.mul_zero]
      | add z z' hz hz' => simp only [map_add, K₀Ring.mul_add, hz, hz']
      | neg z hz => simp only [map_neg, K₀Ring.mul_neg, hz]
    | zero => simp only [map_zero, K₀Ring.mul_zero, K₀Ring.zero_mul]
    | add y y' hy hy' => simp only [map_add, K₀Ring.mul_add, K₀Ring.add_mul, hy, hy']
    | neg y hy => simp only [map_neg, K₀Ring.mul_neg, K₀Ring.neg_mul, hy]
  | zero => simp only [map_zero, K₀Ring.zero_mul]
  | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]


-- @@ L225-237 verbatim
protected theorem mul_assoc (x y z : K₀Ring B) : x * y * z = x * (y * z) := by
  induction x using induction_on with
  | zero => simp only [K₀Ring.zero_mul]
  | of a b x =>
    induction y using induction_on with
    | zero => simp only [K₀Ring.zero_mul, K₀Ring.mul_zero]
    | of c d y =>
      induction z using induction_on with
      | zero => simp only [K₀Ring.mul_zero]
      | of e e' z => exact mul_assoc_of x y z
      | add z z' hz hz' => simp only [K₀Ring.mul_add, hz, hz']
    | add y y' hy hy' => simp only [K₀Ring.mul_add, K₀Ring.add_mul, hy, hy']
  | add x x' hx hx' => simp only [K₀Ring.add_mul, hx, hx']


-- @@ L239-247 verbatim
/-- **Brundan–Ellis, end of §6.** The Grothendieck ring of an additive 2-category is a
(non-unital, associative) ring, with `[G] · [F] = [F ≫ G]`. -/
instance instNonUnitalRing : NonUnitalRing (K₀Ring B) :=
  { (inferInstance : AddCommGroup (K₀Ring B)) with
    mul_assoc := K₀Ring.mul_assoc
    left_distrib := K₀Ring.mul_add
    right_distrib := K₀Ring.add_mul
    zero_mul := K₀Ring.zero_mul
    mul_zero := K₀Ring.mul_zero }


-- @@ L249-249 verbatim
/-! ### The distinguished idempotents `1_λ` -/


-- @@ L251-252 verbatim
/-- The idempotent `1_λ := [𝟙 λ]`. -/
def one (a : B) : K₀Ring B := mk (𝟙 a)


-- @@ L254-262 verbatim
theorem one_mul_of (x : K₀ (a ⟶ b)) : one b * of a b x = of a b x := by
  induction x using K₀.induction_on with
  | mk f =>
    change mk (𝟙 b) * mk f = mk f
    rw [mk_mul_mk]
    exact mk_eq_mk_of_iso (ρ_ f)
  | zero => simp only [map_zero, K₀Ring.mul_zero]
  | add x x' hx hx' => simp only [map_add, K₀Ring.mul_add, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.mul_neg, hx]


-- @@ L264-272 verbatim
theorem of_mul_one (x : K₀ (a ⟶ b)) : of a b x * one a = of a b x := by
  induction x using K₀.induction_on with
  | mk f =>
    change mk f * mk (𝟙 a) = mk f
    rw [mk_mul_mk]
    exact mk_eq_mk_of_iso (λ_ f)
  | zero => simp only [map_zero, K₀Ring.zero_mul]
  | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]


-- @@ L274-275 verbatim
theorem one_mul_of_of_ne {c : B} (h : c ≠ b) (x : K₀ (a ⟶ b)) : one c * of a b x = 0 := by
  rw [one, mk, of_mul_of, mulOf_of_ne (Ne.symm h)]


-- @@ L277-278 verbatim
theorem of_mul_one_of_ne {c : B} (h : c ≠ a) (x : K₀ (a ⟶ b)) : of a b x * one c = 0 := by
  rw [one, mk, of_mul_of, mulOf_of_ne h]


-- @@ L280-281 verbatim
/-- `1_λ` is idempotent. -/
theorem one_mul_one_self (a : B) : one a * one a = one a := one_mul_of (K₀.mk (𝟙 a))


-- @@ L283-285 verbatim
/-- The `1_λ` are mutually orthogonal. -/
theorem one_mul_one_of_ne {a b : B} (h : a ≠ b) : one a * one b = 0 :=
  one_mul_of_of_ne h (K₀.mk (𝟙 b))


-- @@ L287-290 verbatim
theorem finset_sum_one_mul_of (s : Finset B) (hb : b ∈ s) (x : K₀ (a ⟶ b)) :
    (∑ c ∈ s, one c) * of a b x = of a b x := by
  rw [Finset.sum_mul, Finset.sum_eq_single b (fun c _ hc => one_mul_of_of_ne hc x)
    (fun h => absurd hb h), one_mul_of]


-- @@ L292-295 verbatim
theorem of_mul_finset_sum_one (s : Finset B) (ha : a ∈ s) (x : K₀ (a ⟶ b)) :
    of a b x * ∑ c ∈ s, one c = of a b x := by
  rw [Finset.mul_sum, Finset.sum_eq_single a (fun c _ hc => of_mul_one_of_ne hc x)
    (fun h => absurd ha h), of_mul_one]


-- @@ L297-313 verbatim
/-- **Local unitality.** Every element of `K₀Ring B` is fixed by left and right multiplication
by the sum of the idempotents `1_λ` over any large enough finite set of objects. -/
theorem exists_finset_one_mul (x : K₀Ring B) :
    ∃ s : Finset B, ∀ t : Finset B, s ⊆ t →
      (∑ c ∈ t, one c) * x = x ∧ x * ∑ c ∈ t, one c = x := by
  induction x using induction_on with
  | zero => exact ⟨∅, fun _ _ => by simp⟩
  | of a b x =>
    exact ⟨{a, b}, fun t ht => ⟨finset_sum_one_mul_of t (ht (by simp)) x,
      of_mul_finset_sum_one t (ht (by simp)) x⟩⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := hs t (Finset.union_subset_left ht)
    obtain ⟨h1', h2'⟩ := hs' t (Finset.union_subset_right ht)
    exact ⟨by rw [mul_add, h1, h1'], by rw [add_mul, h2, h2']⟩


-- @@ L315-315 verbatim
/-! ## The `Zπ[q, q⁻¹]`-algebra structure for `(Q, Π)`-2-categories -/


-- @@ L317-317 verbatim
section Module


-- @@ L319-319 verbatim
open LaurentPolynomial


-- @@ L321-322 verbatim
variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]
  [QPiTwoCategory R B]


-- @@ L324-324 verbatim
local notation "𝛑" => PiTwoCategory.pi (R := R)

-- @@ L325-325 verbatim
local notation "𝛃" => PiTwoCategory.β (R := R)

-- @@ L326-326 verbatim
local notation "𝐪" => QPiTwoCategory.q (R := R)

-- @@ L327-327 verbatim
local notation "𝐪⁻¹" => QPiTwoCategory.qinv (R := R)

-- @@ L328-328 verbatim
local notation "𝛄" => QPiTwoCategory.γ (R := R)


-- @@ L330-333 verbatim
/-- The endomorphism of `K₀Ring B` acting on `K₀ (a ⟶ b)` by `[F] ↦ [F ≫ t_b]`, for a family
of 1-morphisms `t_b : b → b` (`π`, `q`, `q⁻¹`). -/
def tEnd (t : ∀ b : B, b ⟶ b) : AddMonoid.End (K₀Ring B) :=
  DirectSum.map fun p : B × B => K₀.map (postcomp p.1 (t p.2))


-- @@ L335-337 verbatim
theorem tEnd_of (t : ∀ b : B, b ⟶ b) (x : K₀ (a ⟶ b)) :
    tEnd t (of a b x) = of a b (K₀.map (postcomp a (t b)) x) :=
  DirectSum.map_of _ _ _


-- @@ L339-341 verbatim
theorem tEnd_mk (t : ∀ b : B, b ⟶ b) (f : a ⟶ b) : tEnd t (mk f) = mk (f ≫ t b) := by
  rw [mk, tEnd_of, K₀.map_mk]
  rfl


-- @@ L343-368 verbatim
/-- `[F ≫ t] = [t ≫ F]`-type endomorphisms commute with the multiplication. -/
theorem tEnd_mul (t : ∀ b : B, b ⟶ b) (x y : K₀Ring B) : tEnd t (x * y) = tEnd t x * y := by
  induction x using induction_on with
  | zero => simp only [K₀Ring.zero_mul, map_zero]
  | of a b x =>
    induction y using induction_on with
    | zero => simp only [K₀Ring.mul_zero, map_zero]
    | of c d y =>
      induction x using K₀.induction_on with
      | mk f =>
        induction y using K₀.induction_on with
        | mk g =>
          change tEnd t (mk f * mk g) = tEnd t (mk f) * mk g
          by_cases h : d = a
          · subst h
            rw [mk_mul_mk, tEnd_mk, tEnd_mk, mk_mul_mk]
            exact mk_eq_mk_of_iso (α_ g f (t b))
          · rw [mk_mul_mk_of_ne _ _ h, tEnd_mk, mk_mul_mk_of_ne _ _ h, map_zero]
        | zero => simp only [map_zero, K₀Ring.mul_zero]
        | add y y' hy hy' => simp only [map_add, K₀Ring.mul_add, hy, hy']
        | neg y hy => simp only [map_neg, K₀Ring.mul_neg, hy]
      | zero => simp only [map_zero, K₀Ring.zero_mul]
      | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
      | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]
    | add y y' hy hy' => simp only [K₀Ring.mul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [K₀Ring.add_mul, map_add, hx, hx']


-- @@ L370-395 verbatim
theorem mul_tEnd (t : ∀ b : B, b ⟶ b) (τ : ∀ {a b : B} (f : a ⟶ b), f ≫ t b ≅ t a ≫ f)
    (x y : K₀Ring B) : tEnd t (x * y) = x * tEnd t y := by
  induction x using induction_on with
  | zero => simp only [K₀Ring.zero_mul, map_zero]
  | of a b x =>
    induction y using induction_on with
    | zero => simp only [K₀Ring.mul_zero, map_zero]
    | of c d y =>
      induction x using K₀.induction_on with
      | mk f =>
        induction y using K₀.induction_on with
        | mk g =>
          change tEnd t (mk f * mk g) = mk f * tEnd t (mk g)
          by_cases h : d = a
          · subst h
            rw [mk_mul_mk, tEnd_mk, tEnd_mk, mk_mul_mk]
            exact mk_eq_mk_of_iso (α_ g f _ ≪≫ whiskerLeftIso g (τ f) ≪≫ (α_ g _ f).symm)
          · rw [mk_mul_mk_of_ne _ _ h, tEnd_mk, mk_mul_mk_of_ne _ _ h, map_zero]
        | zero => simp only [map_zero, K₀Ring.mul_zero]
        | add y y' hy hy' => simp only [map_add, K₀Ring.mul_add, hy, hy']
        | neg y hy => simp only [map_neg, K₀Ring.mul_neg, hy]
      | zero => simp only [map_zero, K₀Ring.zero_mul]
      | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
      | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]
    | add y y' hy hy' => simp only [K₀Ring.mul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [K₀Ring.add_mul, map_add, hx, hx']


-- @@ L397-407 verbatim
/-- `[F ≫ t_μ] = [t_μ] · [F]`: the endomorphism `tEnd t` is left multiplication by `[t_μ]` on
`K₀ (λ ⟶ μ)`. -/
theorem tEnd_of_eq_mk_mul (t : ∀ b : B, b ⟶ b) (x : K₀ (a ⟶ b)) :
    tEnd t (of a b x) = mk (t b) * of a b x := by
  induction x using K₀.induction_on with
  | mk f =>
    change tEnd t (mk f) = mk (t b) * mk f
    rw [tEnd_mk, mk_mul_mk]
  | zero => simp only [map_zero, K₀Ring.mul_zero]
  | add x x' hx hx' => simp only [map_add, K₀Ring.mul_add, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.mul_neg, hx]


-- @@ L409-420 verbatim
/-- `[F ≫ t_μ] = [F] · [t_λ]` when `F t_μ ≅ t_λ F`: the endomorphism `tEnd t` is right
multiplication by `[t_λ]` on `K₀ (λ ⟶ μ)`. -/
theorem tEnd_of_eq_mul_mk (t : ∀ b : B, b ⟶ b) (τ : ∀ {a b : B} (f : a ⟶ b), f ≫ t b ≅ t a ≫ f)
    (x : K₀ (a ⟶ b)) : tEnd t (of a b x) = of a b x * mk (t a) := by
  induction x using K₀.induction_on with
  | mk f =>
    change tEnd t (mk f) = mk f * mk (t a)
    rw [tEnd_mk, mk_mul_mk]
    exact mk_eq_mk_of_iso (τ f)
  | zero => simp only [map_zero, K₀Ring.zero_mul]
  | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]


-- @@ L422-426 verbatim
/-- The isomorphism `F q_μ⁻¹ ≅ q_λ⁻¹ F` derived from `γ_F`, `ii` and `jj`. -/
def γinvIso (f : a ⟶ b) : f ≫ 𝐪⁻¹ b ≅ 𝐪⁻¹ a ≫ f :=
  (λ_ _).symm ≪≫ whiskerRightIso (QPiTwoCategory.jj (R := R) a).symm _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ ((α_ _ _ _).symm ≪≫ whiskerRightIso (𝛄 f).symm _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (QPiTwoCategory.ii (R := R) b) ≪≫ ρ_ _)


-- @@ L428-450 verbatim
set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- The ring homomorphism `Zπ[q, q⁻¹] → End(K₀Ring B)` acting on each summand `K₀ (λ ⟶ μ)`
through the `Zπ[q, q⁻¹]`-module structure of `K₀` of the `(Q, Π)`-category `Hom(λ, μ)`
(`K₀.laurentEnd`). -/
def laurentEnd : LaurentPolynomial Zπ →+* AddMonoid.End (K₀Ring B) where
  toFun r := DirectSum.map fun p : B × B => K₀.laurentEnd R (p.1 ⟶ p.2) r
  map_one' := AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    rw [DirectSum.map_apply, map_one]
    rfl
  map_mul' r s := AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    show (DirectSum.map (fun p : B × B => K₀.laurentEnd R (p.1 ⟶ p.2) (r * s)) x) p =
      (DirectSum.map (fun p : B × B => K₀.laurentEnd R (p.1 ⟶ p.2) r)
        (DirectSum.map (fun p : B × B => K₀.laurentEnd R (p.1 ⟶ p.2) s) x)) p
    rw [DirectSum.map_apply, DirectSum.map_apply, DirectSum.map_apply, map_mul]
    rfl
  map_zero' := AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    rw [DirectSum.map_apply, map_zero]
    rfl
  map_add' r s := AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    rw [AddMonoidHom.add_apply, DirectSum.add_apply, DirectSum.map_apply, DirectSum.map_apply,
      DirectSum.map_apply, map_add]
    rfl


-- @@ L452-454 verbatim
theorem laurentEnd_apply (r : LaurentPolynomial Zπ) (x : K₀Ring B) (p : B × B) :
    laurentEnd R r x p = K₀.laurentEnd R (p.1 ⟶ p.2) r (x p) :=
  DirectSum.map_apply _ _ _


-- @@ L456-458 verbatim
theorem laurentEnd_of (r : LaurentPolynomial Zπ) (x : K₀ (a ⟶ b)) :
    laurentEnd R r (of a b x) = of a b (K₀.laurentEnd R (a ⟶ b) r x) :=
  DirectSum.map_of _ _ _


-- @@ L460-464 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem laurentEnd_C_π : laurentEnd R (B := B) (C Zπ.π) = tEnd 𝛑 :=
  AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    rw [laurentEnd_apply, K₀.laurentEnd_C, Zπ.toEnd_π, tEnd, DirectSum.map_apply]
    rfl


-- @@ L466-470 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem laurentEnd_T_one : laurentEnd R (B := B) (T 1) = tEnd 𝐪 :=
  AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    rw [laurentEnd_apply, K₀.laurentEnd_T, zpow_one, tEnd, DirectSum.map_apply]
    rfl


-- @@ L472-476 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem laurentEnd_T_neg_one : laurentEnd R (B := B) (T (-1)) = tEnd 𝐪⁻¹ :=
  AddMonoidHom.ext fun x => DirectSum.ext fun p => by
    rw [laurentEnd_apply, K₀.laurentEnd_T, zpow_neg_one, tEnd, DirectSum.map_apply]
    rfl


-- @@ L478-484 verbatim
variable (R) in
/-- **Brundan–Ellis, end of §6.** The Grothendieck ring of a `(Q, Π)`-2-category is a module
over `Zπ[q, q⁻¹]`, with `π` and `q` acting on the summand `K₀ (λ ⟶ μ)` by `[F] ↦ [F ≫ π_μ]`
and `[F] ↦ [F ≫ q_μ]` (the paper's `[π_μ F]`, `[q_μ F]`). -/
@[instance_reducible]
def moduleLaurent : Module (LaurentPolynomial Zπ) (K₀Ring B) :=
  Module.compHom (K₀Ring B) (laurentEnd R (B := B))


-- @@ L486-488 verbatim
theorem smul_def (r : LaurentPolynomial Zπ) (x : K₀Ring B) :
    letI := moduleLaurent R (B := B)
    r • x = laurentEnd R r x := rfl


-- @@ L490-496 verbatim
/-- The module structure restricts on each summand to that of `K₀ (λ ⟶ μ)`
(`K₀.moduleLaurent` for the `(Q, Π)`-category `Hom(λ, μ)`). -/
theorem smul_of (r : LaurentPolynomial Zπ) (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    letI := K₀.moduleLaurent R (a ⟶ b)
    r • of a b x = of a b (r • x) :=
  laurentEnd_of r x


-- @@ L498-503 verbatim
/-- `π` acts on `1_μ K₀ 1_λ` by left multiplication by `[π_μ]`. -/
theorem C_π_smul_of (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (C Zπ.π : LaurentPolynomial Zπ) • of a b x = mk (𝛑 b) * of a b x := by
  show laurentEnd R (C Zπ.π) (of a b x) = _
  rw [laurentEnd_C_π, tEnd_of_eq_mk_mul]


-- @@ L505-510 verbatim
/-- `π` acts on `1_μ K₀ 1_λ` by right multiplication by `[π_λ]` (via `β`). -/
theorem C_π_smul_of' (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (C Zπ.π : LaurentPolynomial Zπ) • of a b x = of a b x * mk (𝛑 a) := by
  show laurentEnd R (C Zπ.π) (of a b x) = _
  rw [laurentEnd_C_π, tEnd_of_eq_mul_mk 𝛑 (fun f => 𝛃 f)]


-- @@ L512-517 verbatim
/-- `q` acts on `1_μ K₀ 1_λ` by left multiplication by `[q_μ]`. -/
theorem T_smul_of (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T 1 : LaurentPolynomial Zπ) • of a b x = mk (𝐪 b) * of a b x := by
  show laurentEnd R (T 1) (of a b x) = _
  rw [laurentEnd_T_one, tEnd_of_eq_mk_mul]


-- @@ L519-524 verbatim
/-- `q` acts on `1_μ K₀ 1_λ` by right multiplication by `[q_λ]` (via `γ`). -/
theorem T_smul_of' (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T 1 : LaurentPolynomial Zπ) • of a b x = of a b x * mk (𝐪 a) := by
  show laurentEnd R (T 1) (of a b x) = _
  rw [laurentEnd_T_one, tEnd_of_eq_mul_mk 𝐪 (fun f => 𝛄 f)]


-- @@ L526-531 verbatim
/-- `q⁻¹` acts on `1_μ K₀ 1_λ` by left multiplication by `[q_μ⁻¹]`. -/
theorem T_neg_one_smul_of (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T (-1) : LaurentPolynomial Zπ) • of a b x = mk (𝐪⁻¹ b) * of a b x := by
  show laurentEnd R (T (-1)) (of a b x) = _
  rw [laurentEnd_T_neg_one, tEnd_of_eq_mk_mul]


-- @@ L533-538 verbatim
/-- `q⁻¹` acts on `1_μ K₀ 1_λ` by right multiplication by `[q_λ⁻¹]`. -/
theorem T_neg_one_smul_of' (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T (-1) : LaurentPolynomial Zπ) • of a b x = of a b x * mk (𝐪⁻¹ a) := by
  show laurentEnd R (T (-1)) (of a b x) = _
  rw [laurentEnd_T_neg_one, tEnd_of_eq_mul_mk 𝐪⁻¹ (fun f => γinvIso f)]


-- @@ L540-540 verbatim
/-! ### Compatibility of the module structure with the multiplication -/


-- @@ L542-544 verbatim
/-- An endomorphism commuting with left and right multiplications. -/
def IsCentral (φ : AddMonoid.End (K₀Ring B)) : Prop :=
  ∀ x y : K₀Ring B, φ (x * y) = φ x * y ∧ φ (x * y) = x * φ y


-- @@ L546-546 verbatim
theorem isCentral_one : IsCentral (1 : AddMonoid.End (K₀Ring B)) := fun _ _ => ⟨rfl, rfl⟩


-- @@ L548-550 verbatim
theorem isCentral_zero : IsCentral (0 : AddMonoid.End (K₀Ring B)) := fun x y =>
  ⟨by rw [AddMonoid.End.zero_apply, AddMonoid.End.zero_apply, zero_mul],
    by rw [AddMonoid.End.zero_apply, AddMonoid.End.zero_apply, mul_zero]⟩


-- @@ L552-557 verbatim
theorem IsCentral.add {φ ψ : AddMonoid.End (K₀Ring B)} (hφ : IsCentral φ) (hψ : IsCentral ψ) :
    IsCentral (φ + ψ) := fun x y => by
  obtain ⟨h1, h2⟩ := hφ x y
  obtain ⟨h3, h4⟩ := hψ x y
  exact ⟨by change φ (x * y) + ψ (x * y) = (φ x + ψ x) * y; rw [h1, h3, add_mul],
    by change φ (x * y) + ψ (x * y) = x * (φ y + ψ y); rw [h2, h4, mul_add]⟩


-- @@ L559-563 verbatim
theorem IsCentral.neg {φ : AddMonoid.End (K₀Ring B)} (hφ : IsCentral φ) : IsCentral (-φ) :=
  fun x y => by
  obtain ⟨h1, h2⟩ := hφ x y
  exact ⟨by change -φ (x * y) = -φ x * y; rw [h1, neg_mul],
    by change -φ (x * y) = x * -φ y; rw [h2, mul_neg]⟩


-- @@ L565-571 verbatim
theorem IsCentral.mul {φ ψ : AddMonoid.End (K₀Ring B)} (hφ : IsCentral φ) (hψ : IsCentral ψ) :
    IsCentral (φ * ψ) := fun x y => by
  obtain ⟨h3, h4⟩ := hψ x y
  obtain ⟨h1, _⟩ := hφ (ψ x) y
  obtain ⟨_, h2⟩ := hφ x (ψ y)
  exact ⟨by change φ (ψ (x * y)) = φ (ψ x) * y; rw [h3, h1],
    by change φ (ψ (x * y)) = x * φ (ψ y); rw [h4, h2]⟩


-- @@ L573-577 verbatim
theorem isCentral_intCast (n : ℤ) : IsCentral ((n : ℤ) : AddMonoid.End (K₀Ring B)) := by
  induction n using Int.induction_on with
  | zero => rw [Int.cast_zero]; exact isCentral_zero
  | succ n ih => rw [Int.cast_add, Int.cast_one]; exact ih.add isCentral_one
  | pred n ih => rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]; exact ih.add isCentral_one.neg


-- @@ L579-580 verbatim
theorem isCentral_tEnd_π : IsCentral (tEnd (B := B) 𝛑) := fun x y =>
  ⟨tEnd_mul 𝛑 x y, mul_tEnd 𝛑 (fun f => 𝛃 f) x y⟩


-- @@ L582-583 verbatim
theorem isCentral_tEnd_q : IsCentral (tEnd (B := B) 𝐪) := fun x y =>
  ⟨tEnd_mul 𝐪 x y, mul_tEnd 𝐪 (fun f => 𝛄 f) x y⟩


-- @@ L585-586 verbatim
theorem isCentral_tEnd_qinv : IsCentral (tEnd (B := B) 𝐪⁻¹) := fun x y =>
  ⟨tEnd_mul 𝐪⁻¹ x y, mul_tEnd 𝐪⁻¹ (fun f => γinvIso f) x y⟩


-- @@ L588-593 verbatim
theorem isCentral_laurentEnd_T (n : ℤ) : IsCentral (laurentEnd R (B := B) (T n)) := by
  induction n using Int.induction_on with
  | zero => rw [T_zero, map_one]; exact isCentral_one
  | succ n ih => rw [T_add, map_mul, laurentEnd_T_one]; exact ih.mul (isCentral_tEnd_q (R := R))
  | pred n ih =>
    rw [T_sub, map_mul, laurentEnd_T_neg_one]; exact ih.mul (isCentral_tEnd_qinv (R := R))


-- @@ L595-599 verbatim
theorem isCentral_laurentEnd_C (r : Zπ) : IsCentral (laurentEnd R (B := B) (C r)) := by
  obtain ⟨i, j, rfl⟩ := Zπ.exists_eq_add_mul_π r
  rw [map_add, map_mul, map_intCast, map_intCast, map_add, map_mul, map_intCast, map_intCast,
    laurentEnd_C_π]
  exact (isCentral_intCast i).add ((isCentral_intCast j).mul (isCentral_tEnd_π (R := R)))


-- @@ L601-604 verbatim
theorem isCentral_laurentEnd (r : LaurentPolynomial Zπ) : IsCentral (laurentEnd R (B := B) r) := by
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | C_mul_T n a => rw [map_mul]; exact (isCentral_laurentEnd_C a).mul (isCentral_laurentEnd_T n)


-- @@ L606-611 verbatim
/-- **Brundan–Ellis, end of §6.** The `Zπ[q, q⁻¹]`-module structure is compatible with the
multiplication: `K₀Ring B` is a `Zπ[q, q⁻¹]`-algebra. -/
theorem smul_mul (r : LaurentPolynomial Zπ) (x y : K₀Ring B) :
    letI := moduleLaurent R (B := B)
    (r • x) * y = r • (x * y) :=
  ((isCentral_laurentEnd r) x y).1.symm


-- @@ L613-616 verbatim
theorem mul_smul (r : LaurentPolynomial Zπ) (x y : K₀Ring B) :
    letI := moduleLaurent R (B := B)
    x * (r • y) = r • (x * y) :=
  ((isCentral_laurentEnd r) x y).2.symm


-- @@ L618-618 verbatim
end Module


-- @@ L620-620 verbatim
end K₀Ring


-- @@ L622-622 verbatim
end Ring


-- @@ L624-624 verbatim
/-! ## The Grothendieck ring of `GSKAR(𝔄)` -/


-- @@ L626-626 verbatim
section GSKAR


-- @@ L628-628 verbatim
open LaurentPolynomial


-- @@ L630-633 verbatim
variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]


-- @@ L635-635 verbatim
namespace GSKAR


-- @@ L637-640 verbatim
/-- **Brundan–Ellis, end of §6.** The Grothendieck ring `K₀(GSKAR(𝔄))` of the graded super
Karoubi envelope of a graded 2-supercategory is a locally unital ring with the distinguished
idempotents `1_λ` (`K₀Ring.one`). -/
example : NonUnitalRing (K₀Ring (GSKAR R B)) := inferInstance


-- @@ L642-643 verbatim
/-- The summand `1_μ K₀(GSKAR(𝔄)) 1_λ` is `K₀(GSKar(Hom_𝔄(λ, μ)))`. -/
theorem K₀_hom_eq (a b : B) : K₀ (mkObj R B a ⟶ mkObj R B b) = K₀ (GSKar R (a ⟶ b)) := rfl


-- @@ L645-648 verbatim
/-- **Brundan–Ellis, end of §6.** `K₀(GSKAR(𝔄))` is a `Zπ[q, q⁻¹]`-algebra. -/
@[instance_reducible]
def moduleLaurent : Module (LaurentPolynomial Zπ) (K₀Ring (GSKAR R B)) :=
  K₀Ring.moduleLaurent R


-- @@ L650-653 verbatim
theorem smul_mul (r : LaurentPolynomial Zπ) (x y : K₀Ring (GSKAR R B)) :
    letI := moduleLaurent R B
    (r • x) * y = r • (x * y) :=
  K₀Ring.smul_mul r x y


-- @@ L655-658 verbatim
theorem mul_smul (r : LaurentPolynomial Zπ) (x y : K₀Ring (GSKAR R B)) :
    letI := moduleLaurent R B
    x * (r • y) = r • (x * y) :=
  K₀Ring.mul_smul r x y


-- @@ L660-660 verbatim
variable {R B}


-- @@ L662-670 verbatim
/-- `π` acts on `1_μ K₀ 1_λ` by left multiplication by `[π_μ]`, equivalently by right
multiplication by `[π_λ]`. -/
theorem C_π_smul_of {a b : B} (x : K₀ (mkObj R B a ⟶ mkObj R B b)) :
    letI := moduleLaurent R B
    (C Zπ.π : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.mk (PiTwoCategory.pi (R := R) (mkObj R B b)) * K₀Ring.of _ _ x ∧
      (C Zπ.π : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.of _ _ x * K₀Ring.mk (PiTwoCategory.pi (R := R) (mkObj R B a)) :=
  ⟨K₀Ring.C_π_smul_of x, K₀Ring.C_π_smul_of' x⟩


-- @@ L672-680 verbatim
/-- `q` acts on `1_μ K₀ 1_λ` by left multiplication by `[q_μ]`, equivalently by right
multiplication by `[q_λ]`. -/
theorem T_smul_of {a b : B} (x : K₀ (mkObj R B a ⟶ mkObj R B b)) :
    letI := moduleLaurent R B
    (T 1 : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.mk (QPiTwoCategory.q (R := R) (mkObj R B b)) * K₀Ring.of _ _ x ∧
      (T 1 : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.of _ _ x * K₀Ring.mk (QPiTwoCategory.q (R := R) (mkObj R B a)) :=
  ⟨K₀Ring.T_smul_of x, K₀Ring.T_smul_of' x⟩


-- @@ L682-682 verbatim
end GSKAR


-- @@ L684-684 verbatim
end GSKAR


-- @@ L686-686 verbatim
end StringDiagrams


-- @@ L688-688 verbatim
end
