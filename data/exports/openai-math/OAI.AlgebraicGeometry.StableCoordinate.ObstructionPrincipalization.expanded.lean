import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import OAI.AlgebraicGeometry.StableCoordinate.BundleCharts
import OAI.AlgebraicGeometry.StableCoordinate.BundlePrincipalization
import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-16 verbatim
/-!
# Principalization and invariant transport in the exact obstruction rings

The generic polynomial identity proved in `BundlePrincipalization` is instantiated
here in the source's actual rings `B` and `C`, through the injective two-chart
base map.  The final lemmas prove the last step of source Proposition `prop:lift`:
once an actual locally nilpotent extension has been constructed, a nonzero
invariant in the source ideal forces it to annihilate `v`.
-/


-- @@ L18-18 verbatim
namespace StableCoordinate.Obstruction


-- @@ L20-20 verbatim
variable (k : Type*) [CommRing k]


-- @@ L22-30 verbatim
/-- Evaluation at an actual determinant-one matrix supplies a scalar retraction. -/
noncomputable def determinantBasepoint : C k →ₐ[k] k :=
  Ideal.Quotient.liftₐ (idealC k) (MvPolynomial.aeval ![1, 0, 0, 1, 0]) (by
    intro p hp
    have hs : idealC k ≤ RingHom.ker
        (MvPolynomial.aeval ![(1 : k), 0, 0, 1, 0]).toRingHom := by
      rw [idealC, Ideal.span_singleton_le_iff_mem]
      simp [RingHom.mem_ker, determinantRelation]
    exact hs hp)


-- @@ L32-37 verbatim
/-- The determinant coordinate ring inherits characteristic zero from its
coefficient ring; this is proved using the displayed scalar retraction. -/
instance determinantCharZero [CharZero k] : CharZero (C k) where
  cast_injective n m h := by
    have hh := congrArg (determinantBasepoint k) h
    simpa only [map_natCast, Nat.cast_inj] using hh


-- @@ L39-40 verbatim
/-- The source's injective map `B → C`, with the canonical obstruction-ring API. -/
noncomputable abbrev baseMap : B k →ₐ[k] C k := BundleCharts.baseMap k


-- @@ L42-45 verbatim
@[simp] theorem baseMap_bX (i : Fin 4) :
    baseMap k (bX k i) =
      ![cX k 0 * cX k 2, cX k 1 * cX k 3, cX k 1 * cX k 2, cX k 4] i :=
  BundleCharts.baseMap_qgen k i


-- @@ L47-49 verbatim
/-- Injectivity is proved by two explicit local sections, not assumed. -/
theorem baseMap_injective : Function.Injective (baseMap k) :=
  BundleCharts.baseMap_injective k


-- @@ L51-53 verbatim
@[simp] theorem baseMap_sB :
    baseMap k (sB k) = Bundle.s (cX k 0) (cX k 1) (cX k 2) (cX k 3) (cX k 4) := by
  simp [sB, Bundle.s]


-- @@ L55-57 verbatim
@[simp] theorem baseMap_f0 :
    baseMap k (f0 k) = Bundle.f₀ (cX k 0) (cX k 1) (cX k 2) (cX k 3) (cX k 4) := by
  simp [f0, Bundle.f₀]


-- @@ L59-61 verbatim
@[simp] theorem baseMap_g0 :
    baseMap k (g0 k) = Bundle.g₀ (cX k 0) (cX k 1) (cX k 2) (cX k 3) (cX k 4) := by
  simp [g0, Bundle.g₀]


-- @@ L63-70 verbatim
/-- Exact source principalization: the extended ideal `IC` is `(v)`. -/
theorem map_I_eq_span_v :
    Ideal.map (baseMap k).toRingHom (I k) = Ideal.span ({v k} : Set (C k)) := by
  rw [I, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change Ideal.span ({baseMap k (f0 k), baseMap k (g0 k)} : Set (C k)) = _
  rw [baseMap_f0, baseMap_g0]
  exact Bundle.principalization (cX k 0) (cX k 1) (cX k 2) (cX k 3) (cX k 4)
    (sub_eq_zero.mp (c_relation k))


-- @@ L72-79 verbatim
/-- Every element of the distinguished ideal admits the required factorization
in the total ring, with its actual image under the base map. -/
theorem baseMap_factor_of_mem_I {h : B k} (hh : h ∈ I k) :
    ∃ q : C k, baseMap k h = v k * q := by
  have hm : baseMap k h ∈ Ideal.map (baseMap k).toRingHom (I k) :=
    Ideal.mem_map_of_mem _ hh
  rw [map_I_eq_span_v, Ideal.mem_span_singleton] at hm
  exact hm


-- @@ L81-81 verbatim
section Derivations


-- @@ L83-83 verbatim
variable {k}

-- @@ L84-84 verbatim
variable (D : Derivation k (B k) (B k)) (D' : Derivation k (C k) (C k))


-- @@ L86-95 verbatim
/-- An actual extension of a nonzero derivation remains nonzero because the
source ring embeds in the total ring. -/
theorem extension_ne_zero
    (hD : D ≠ 0) (hExt : ∀ b, D' (baseMap k b) = baseMap k (D b)) : D' ≠ 0 := by
  intro hD'
  apply hD
  ext b
  apply baseMap_injective k
  change baseMap k (D b) = baseMap k 0
  rw [map_zero, ← hExt, hD', Derivation.zero_apply]


-- @@ L97-97 verbatim
variable [IsDomain (C k)] [CharZero k]


-- @@ L99-114 verbatim
/-- The principalized invariant is fixed by any actual locally nilpotent lift.
This is the final factorial-closure argument of source `prop:lift`. -/
theorem extension_annihilates_v
    (hLND : StableCoordinate.IsLocallyNilpotent D')
    (hExt : ∀ b, D' (baseMap k b) = baseMap k (D b))
    {h : B k} (hh : h ∈ I k) (h0 : h ≠ 0) (hFix : D h = 0) : D' (v k) = 0 := by
  obtain ⟨q, hq⟩ := baseMap_factor_of_mem_I k hh
  have hmap : baseMap k h ≠ 0 := by
    intro hz
    apply h0
    exact baseMap_injective k (by simpa using hz)
  have hprod : v k * q ≠ 0 := by rwa [← hq]
  have hv : v k ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hq0 : q ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hFixed : D' (v k * q) = 0 := by rw [← hq, hExt, hFix, map_zero]
  exact (StableCoordinate.lnd_factorial_closure D' hLND hv hq0 hFixed).1


-- @@ L116-124 verbatim
/-- The two conclusions used by rigidity after constructing the lifted action. -/
theorem extension_nonzero_and_annihilates_v
    (hD : D ≠ 0) (hLND : StableCoordinate.IsLocallyNilpotent D')
    (hExt : ∀ b, D' (baseMap k b) = baseMap k (D b))
    (hInv : ∃ h : B k, h ∈ I k ∧ h ≠ 0 ∧ D h = 0) :
    D' ≠ 0 ∧ D' (v k) = 0 := by
  obtain ⟨h, hh, h0, hFix⟩ := hInv
  exact ⟨extension_ne_zero D D' hD hExt,
    extension_annihilates_v D D' hLND hExt hh h0 hFix⟩


-- @@ L126-126 verbatim
end Derivations


-- @@ L128-128 verbatim
end StableCoordinate.Obstruction


-- @@ L130-130 verbatim
end OAI
