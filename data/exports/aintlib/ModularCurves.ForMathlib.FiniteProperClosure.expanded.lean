import ModularCurves.ForMathlib.FiniteProperProduct
import ModularCurves.ForMathlib.SchemeTheoreticImage


-- @@ L4-9 verbatim
/-!
# Scheme-theoretic closures in finite products of proper schemes

This file packages the closure of a compatible family of morphisms in a finite product of
proper schemes over a common base.
-/


-- @@ L11-11 verbatim
open CategoryTheory


-- @@ L13-13 verbatim
universe u


-- @@ L15-15 verbatim
namespace AlgebraicGeometry.Scheme.FiniteProperClosure


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
variable {S T : Scheme.{u}} {ι : Type u} [Finite ι]

-- @@ L20-20 verbatim
variable {Z : ι → Scheme.{u}} (p : ∀ i, Z i ⟶ S)

-- @@ L21-21 verbatim
variable (q : T ⟶ S) (f : ∀ i, T ⟶ Z i) (hf : ∀ i, f i ≫ p i = q)


-- @@ L23-25 verbatim
/-- The map from the common open subscheme to the finite proper product. -/
abbrev diagonal : T ⟶ FiniteProperProduct.obj p :=
  FiniteProperProduct.lift p q f hf


-- @@ L27-29 verbatim
/-- The scheme-theoretic closure of the common open subscheme in the finite proper product. -/
abbrev obj : Scheme.{u} :=
  (diagonal p q f hf).image


-- @@ L31-33 verbatim
/-- The closed immersion of the closure into the finite proper product. -/
abbrev inclusion : obj p q f hf ⟶ FiniteProperProduct.obj p :=
  (diagonal p q f hf).imageι


-- @@ L35-37 verbatim
/-- The canonical map from the common open subscheme to its closure. -/
abbrev toClosure : T ⟶ obj p q f hf :=
  (diagonal p q f hf).toImage


-- @@ L39-41 verbatim
/-- The structure map from the closure to the base. -/
abbrev π : obj p q f hf ⟶ S :=
  inclusion p q f hf ≫ FiniteProperProduct.π p


-- @@ L43-45 verbatim
/-- The projection from the closure to the `i`-th proper factor. -/
abbrev proj (i : ι) : obj p q f hf ⟶ Z i :=
  inclusion p q f hf ≫ FiniteProperProduct.proj p i


-- @@ L47-50 verbatim
@[reassoc (attr := simp)]
lemma toClosure_inclusion :
    toClosure p q f hf ≫ inclusion p q f hf = diagonal p q f hf :=
  Scheme.Hom.toImage_imageι _


-- @@ L52-54 verbatim
@[reassoc]
lemma proj_comp (i : ι) : proj p q f hf i ≫ p i = π p q f hf := by
  simp only [proj, π, Category.assoc, FiniteProperProduct.proj_comp]


-- @@ L56-58 verbatim
@[reassoc]
lemma toClosure_proj (i : ι) : toClosure p q f hf ≫ proj p q f hf i = f i := by
  simp only [proj, toClosure_inclusion_assoc, FiniteProperProduct.lift_proj]


-- @@ L60-63 verbatim
/-- The closure is proper over the base. -/
lemma π_isProper (hp : ∀ i, IsProper (p i)) : IsProper (π p q f hf) := by
  letI : IsProper (FiniteProperProduct.π p) := FiniteProperProduct.π_isProper p hp
  infer_instance


-- @@ L65-70 verbatim
/-- The projections from the closure to the proper factors are proper. -/
lemma proj_isProper (hp : ∀ i, IsProper (p i)) (i : ι) :
    IsProper (proj p q f hf i) := by
  letI : IsProper (FiniteProperProduct.proj p i) :=
    FiniteProperProduct.proj_isProper p hp i
  infer_instance


-- @@ L72-75 verbatim
/-- The common open subscheme is scheme-theoretically dense in its closure. -/
lemma toClosure_isSchemeTheoreticallyDominant [QuasiCompact (diagonal p q f hf)] :
    IsSchemeTheoreticallyDominant (toClosure p q f hf) :=
  Scheme.Hom.toImage_isSchemeTheoreticallyDominant _


-- @@ L77-82 verbatim
/-- If the coordinate maps are immersions, the common open subscheme is open in its closure. -/
lemma toClosure_isOpenImmersion [Nonempty ι] (hfi : ∀ i, IsImmersion (f i))
    [QuasiCompact (diagonal p q f hf)] : IsOpenImmersion (toClosure p q f hf) := by
  letI : IsImmersion (diagonal p q f hf) :=
    FiniteProperProduct.lift_isImmersion p q f hf hfi
  infer_instance


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end AlgebraicGeometry.Scheme.FiniteProperClosure
