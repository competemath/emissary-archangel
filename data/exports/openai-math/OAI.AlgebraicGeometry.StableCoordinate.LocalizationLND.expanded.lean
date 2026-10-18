import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-15 verbatim
/-!
# Localization of locally nilpotent derivations at invariants

This module proves the localization step used twice in the manuscript:
Section 3 after equation (gr:iterate), and Section 5 before the univariate
locally nilpotent derivation argument.  Denominators are required to be
annihilated by the derivation; there is no characteristic or domain assumption
for the extension and its local nilpotence.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace StableCoordinate

-- @@ L20-20 verbatim
namespace LocalizationLND


-- @@ L22-22 verbatim
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

-- @@ L23-23 verbatim
variable (D : Derivation k A A) (M : Submonoid A)

-- @@ L24-24 verbatim
variable (hM : ∀ m : M, D (m : A) = 0)


-- @@ L26-26 verbatim
include hM


-- @@ L28-37 verbatim
private theorem numerator_wellDefined {a c : A} {b d : M}
    (h : Localization.r M (a, b) (c, d)) :
    Localization.mk (D a) b = Localization.mk (D c) d := by
  apply Localization.mk_eq_mk_iff.mpr
  obtain ⟨e, he⟩ := Localization.r_iff_exists.mp h
  apply Localization.r_iff_exists.mpr
  refine ⟨e, ?_⟩
  have hd := congrArg D he
  simpa only [Derivation.leibniz, hM, smul_eq_mul, mul_zero, zero_mul,
    add_zero, zero_add] using hd


-- @@ L39-43 verbatim
/-- On fractions with invariant denominators the extension differentiates only
the numerator. -/
def localizeFun (x : Localization M) : Localization M :=
  Localization.liftOn x (fun a b => Localization.mk (D a) b)
    (numerator_wellDefined D M hM)


-- @@ L45-46 verbatim
@[simp] theorem localizeFun_mk (a : A) (b : M) :
    localizeFun D M hM (Localization.mk a b) = Localization.mk (D a) b := rfl


-- @@ L48-55 verbatim
private theorem localizeFun_add (x y : Localization M) :
    localizeFun D M hM (x + y) = localizeFun D M hM x + localizeFun D M hM y := by
  induction x using Localization.induction_on with | H x =>
  induction y using Localization.induction_on with | H y =>
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [Localization.add_mk, localizeFun_mk, map_add,
    Derivation.leibniz, hM, smul_eq_mul, mul_zero, add_zero]


-- @@ L57-58 verbatim
private theorem localizeFun_one : localizeFun D M hM 1 = 0 := by
  rw [← Localization.mk_one, localizeFun_mk, D.map_one_eq_zero, Localization.mk_zero]


-- @@ L60-68 verbatim
private theorem localizeFun_mul (x y : Localization M) :
    localizeFun D M hM (x * y) =
      x * localizeFun D M hM y + y * localizeFun D M hM x := by
  induction x using Localization.induction_on with | H x =>
  induction y using Localization.induction_on with | H y =>
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [Localization.mk_mul, localizeFun_mk, Derivation.leibniz, smul_eq_mul]
  rw [mul_comm d b, Localization.add_mk_self]


-- @@ L70-72 verbatim
private theorem localizeFun_algebraMap (r : k) :
    localizeFun D M hM (algebraMap k (Localization M) r) = 0 := by
  rw [← Localization.mk_algebraMap, localizeFun_mk, D.map_algebraMap, Localization.mk_zero]


-- @@ L74-85 verbatim
/-- Extend a derivation to a localization whose denominators it annihilates. -/
def localize : Derivation k (Localization M) (Localization M) where
  toFun := localizeFun D M hM
  map_add' := localizeFun_add D M hM
  map_smul' r x := by
    simp only [Algebra.smul_def, RingHom.id_apply, localizeFun_mul,
      localizeFun_algebraMap, mul_zero, add_zero]
  map_one_eq_zero' := localizeFun_one D M hM
  leibniz' x y := by
    change localizeFun D M hM (x * y) =
      x * localizeFun D M hM y + y * localizeFun D M hM x
    exact localizeFun_mul D M hM x y


-- @@ L87-88 verbatim
@[simp] theorem localize_mk (a : A) (b : M) :
    localize D M hM (Localization.mk a b) = Localization.mk (D a) b := rfl


-- @@ L90-92 verbatim
@[simp] theorem localize_algebraMap (a : A) :
    localize D M hM (algebraMap A (Localization M) a) =
      algebraMap A (Localization M) (D a) := rfl


-- @@ L94-101 verbatim
/-- Iteration continues to differentiate only the numerator. -/
theorem localize_iterate_mk (n : ℕ) (a : A) (b : M) :
    (localize D M hM : Localization M → Localization M)^[n] (Localization.mk a b) =
      Localization.mk ((D : A → A)^[n] a) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, localize_mk, Function.iterate_succ_apply']


-- @@ L103-113 verbatim
/-- Local nilpotence is preserved on localization at invariant denominators. -/
theorem localize_locallyNilpotent
    (hD : ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0) :
    ∀ x : Localization M, ∃ n : ℕ,
      (localize D M hM : Localization M → Localization M)^[n] x = 0 := by
  intro x
  induction x using Localization.induction_on with | H x =>
  rcases x with ⟨a, b⟩
  obtain ⟨n, hn⟩ := hD a
  refine ⟨n, ?_⟩
  rw [localize_iterate_mk, hn, Localization.mk_zero]



-- @@ L116-116 verbatim
omit hM


-- @@ L118-118 verbatim
section Transport


-- @@ L120-120 verbatim
variable {B : Type*} [CommRing B] [Algebra k B]


-- @@ L122-126 verbatim
/-- Transport a derivation across an algebra equivalence. -/
def transport (e : A ≃ₐ[k] B) : Derivation k B B :=
  D.liftOfRightInverse e.apply_symm_apply (fun a ha => by
    have ha' : a = 0 := e.injective (ha.trans (map_zero e).symm)
    simp [ha'])


-- @@ L128-130 verbatim
@[simp] theorem transport_apply (e : A ≃ₐ[k] B) (a : A) :
    transport D e (e a) = e (D a) :=
  Derivation.liftOfRightInverse_apply _ _ a


-- @@ L132-138 verbatim
/-- Iteration commutes with transport. -/
theorem transport_iterate (e : A ≃ₐ[k] B) (n : ℕ) (a : A) :
    (transport D e : B → B)^[n] (e a) = e ((D : A → A)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, transport_apply, Function.iterate_succ_apply']


-- @@ L140-147 verbatim
/-- Local nilpotence is independent of the chosen algebra presentation. -/
theorem transport_locallyNilpotent (e : A ≃ₐ[k] B)
    (hD : ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0) :
    ∀ b : B, ∃ n : ℕ, (transport D e : B → B)^[n] b = 0 := by
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  obtain ⟨n, hn⟩ := hD a
  exact ⟨n, by rw [transport_iterate, hn, map_zero]⟩


-- @@ L149-156 verbatim
/-- Transport preserves nonzero derivations. -/
theorem transport_ne_zero (e : A ≃ₐ[k] B) (hD : D ≠ 0) : transport D e ≠ 0 := by
  intro h
  apply hD
  ext a
  apply e.injective
  have he := congrArg (fun (d : Derivation k B B) => d (e a)) h
  simpa only [transport_apply, Derivation.zero_apply, map_zero] using he


-- @@ L158-158 verbatim
end Transport


-- @@ L160-160 verbatim
section AnyLocalization

-- @@ L161-161 verbatim
include hM


-- @@ L163-164 verbatim
variable (S : Type*) [CommRing S] [Algebra A S] [IsLocalization M S]
  [Algebra k S] [IsScalarTower k A S]


-- @@ L166-168 verbatim
/-- Extend to any algebra satisfying the localization universal property. -/
def localizeTo : Derivation k S S :=
  transport (localize D M hM) ((Localization.algEquiv M S).restrictScalars k)


-- @@ L170-176 verbatim
@[simp] theorem localizeTo_mk' (a : A) (b : M) :
    localizeTo D M hM S (IsLocalization.mk' S a b) = IsLocalization.mk' S (D a) b := by
  change transport (localize D M hM) ((Localization.algEquiv M S).restrictScalars k)
    (IsLocalization.mk' S a b) = _
  rw [← Localization.algEquiv_mk, ← AlgEquiv.restrictScalars_apply k, transport_apply]
  change Localization.algEquiv M S (localize D M hM (Localization.mk a b)) = _
  rw [localize_mk, Localization.algEquiv_mk]


-- @@ L178-181 verbatim
@[simp] theorem localizeTo_algebraMap (a : A) :
    localizeTo D M hM S (algebraMap A S a) = algebraMap A S (D a) := by
  rw [← IsLocalization.mk'_one (S := S) (M := M) a, localizeTo_mk',
    IsLocalization.mk'_one]


-- @@ L183-187 verbatim
/-- The extension to any localization is locally nilpotent. -/
theorem localizeTo_locallyNilpotent
    (hD : ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0) :
    ∀ s : S, ∃ n : ℕ, (localizeTo D M hM S : S → S)^[n] s = 0 :=
  transport_locallyNilpotent _ _ (localize_locallyNilpotent D M hM hD)


-- @@ L189-197 verbatim
/-- If localization is injective, a nonzero derivation remains nonzero. -/
theorem localizeTo_ne_zero (hinj : Function.Injective (algebraMap A S)) (hD : D ≠ 0) :
    localizeTo D M hM S ≠ 0 := by
  intro h
  apply hD
  ext a
  apply hinj
  have he := congrArg (fun (d : Derivation k S S) => d (algebraMap A S a)) h
  simpa only [localizeTo_algebraMap, Derivation.zero_apply, map_zero] using he


-- @@ L199-199 verbatim
end AnyLocalization



-- @@ L202-202 verbatim
omit hM


-- @@ L204-204 verbatim
section Away


-- @@ L206-206 verbatim
variable (a : A) (ha : D a = 0)


-- @@ L208-213 verbatim
include ha in
/-- Killing one element implies killing all powers used as denominators. -/
theorem annihilates_powers : ∀ m : Submonoid.powers a, D (m : A) = 0 := by
  rintro ⟨m, hm⟩
  obtain ⟨n, rfl⟩ := hm
  simp only [Derivation.leibniz_pow, ha, smul_zero]


-- @@ L215-216 verbatim
variable (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away a S] [Algebra k S] [IsScalarTower k A S]


-- @@ L218-220 verbatim
/-- The common special case of localization at one invariant element. -/
def localizeAway : Derivation k S S :=
  localizeTo D (Submonoid.powers a) (annihilates_powers D a ha) S


-- @@ L222-224 verbatim
@[simp] theorem localizeAway_algebraMap (b : A) :
    localizeAway D a ha S (algebraMap A S b) = algebraMap A S (D b) :=
  localizeTo_algebraMap D (Submonoid.powers a) (annihilates_powers D a ha) S b


-- @@ L226-230 verbatim
/-- Localization at a single invariant preserves local nilpotence. -/
theorem localizeAway_locallyNilpotent
    (hD : ∀ b : A, ∃ n : ℕ, (D : A → A)^[n] b = 0) :
    ∀ s : S, ∃ n : ℕ, (localizeAway D a ha S : S → S)^[n] s = 0 :=
  localizeTo_locallyNilpotent D (Submonoid.powers a) (annihilates_powers D a ha) S hD


-- @@ L232-232 verbatim
end Away


-- @@ L234-234 verbatim
end LocalizationLND

-- @@ L235-235 verbatim
end StableCoordinate


-- @@ L237-237 verbatim
end


-- @@ L239-239 verbatim
end OAI
