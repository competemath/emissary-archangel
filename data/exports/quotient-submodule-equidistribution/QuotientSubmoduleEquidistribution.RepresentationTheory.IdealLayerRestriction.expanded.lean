import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import QuotientSubmoduleEquidistribution.RepresentationTheory.StandardQHSemantics


-- @@ L4-4 verbatim
noncomputable section


-- @@ L6-6 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L7-7 verbatim
open MulOpposite


-- @@ L9-9 verbatim
namespace QuotientSubmoduleEquidistribution.Tsukamoto


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
variable {A : Type u} [Ring A]


-- @@ L15-22 verbatim
/-- Inclusion of one two-sided ideal into another as right modules. -/
def rightIdealInclusion
    (J I : TwoSidedIdeal A) (hJI : J ≤ I) :
    ModuleCat.of Aᵐᵒᵖ J ⟶ ModuleCat.of Aᵐᵒᵖ I :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ⟨x, hJI x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }


-- @@ L24-29 verbatim
instance rightIdealInclusion_mono
    (J I : TwoSidedIdeal A) (hJI : J ≤ I) :
    Mono (rightIdealInclusion J I hJI) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  simpa [rightIdealInclusion] using hxy


-- @@ L31-69 verbatim
/-- Under a surjective ring homomorphism, the two-sided span of the image
of an ideal is already its literal image. -/
theorem mem_twoSidedIdeal_map_iff_of_surjective
    {B : Type u} [Ring B]
    (f : A →+* B) (hf : Function.Surjective f)
    (I : TwoSidedIdeal A) (y : B) :
    y ∈ TwoSidedIdeal.map f I ↔
      ∃ x : A, x ∈ I ∧ f x = y := by
  constructor
  · intro hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨x, hx, rfl⟩
    | zero =>
        exact ⟨0, I.zero_mem, map_zero f⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, I.add_mem ha hb, map_add f a b⟩
    | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨-a, I.neg_mem ha, map_neg f a⟩
    | left_absorb b y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨c, rfl⟩ := hf b
        exact
          ⟨c * a, I.mul_mem_left c a ha,
            map_mul f c a⟩
    | right_absorb b y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨c, rfl⟩ := hf b
        exact
          ⟨a * c, I.mul_mem_right a c ha,
            map_mul f a c⟩
  · rintro ⟨x, hx, rfl⟩
    exact
      TwoSidedIdeal.subset_span
        ⟨x, hx, rfl⟩


-- @@ L71-71 verbatim
variable (J I : TwoSidedIdeal A)


-- @@ L73-73 verbatim
local notation "B" => A ⧸ J.asIdeal

-- @@ L74-74 verbatim
local notation "q" => Ideal.Quotient.mk J.asIdeal

-- @@ L75-75 verbatim
local notation "Ibar" => quotientImage I J


-- @@ L77-82 verbatim
/-- The image ideal in `A/J`, regarded again as a right `A`-module. -/
abbrev restrictedQuotientImageRightModule :
    ModuleCat.{u} Aᵐᵒᵖ :=
  (ModuleCat.restrictScalars
    (RingHom.op (Ideal.Quotient.mk J.asIdeal))).obj
      (ModuleCat.of Bᵐᵒᵖ Ibar)


-- @@ L84-95 verbatim
/-- The quotient map from `I` to its image ideal in `A/J`, linear after
restriction of scalars. -/
def rightIdealToRestrictedQuotientImage :
    I →ₗ[Aᵐᵒᵖ] restrictedQuotientImageRightModule J I where
  toFun x :=
    ⟨q x.1,
      TwoSidedIdeal.subset_span
        ⟨x.1, x.property, rfl⟩⟩
  map_add' x y := Subtype.ext (map_add q x.1 y.1)
  map_smul' r x := by
    apply Subtype.ext
    exact map_mul q x.1 (unop r)


-- @@ L97-105 verbatim
theorem rightIdealToRestrictedQuotientImage_surjective :
    Function.Surjective
      (rightIdealToRestrictedQuotientImage J I) := by
  intro y
  obtain ⟨x, hx, hxy⟩ :=
    (mem_twoSidedIdeal_map_iff_of_surjective q
      Ideal.Quotient.mk_surjective I y.1).mp y.2
  exact
    ⟨⟨x, hx⟩, Subtype.ext hxy⟩


-- @@ L107-121 verbatim
theorem range_rightIdealInclusion_eq_ker (hJI : J ≤ I) :
    LinearMap.range (rightIdealInclusion J I hJI).hom =
      LinearMap.ker (rightIdealToRestrictedQuotientImage J I) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr z.property
  · intro hy
    rw [LinearMap.mem_ker] at hy
    have hyval : q y.1 = 0 := congrArg Subtype.val hy
    have hyJ : y.1 ∈ J.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp hyval
    exact ⟨⟨y.1, hyJ⟩, Subtype.ext rfl⟩


-- @@ L123-134 verbatim
/-- The categorical right-ideal layer `I/J` is the image ideal of `I`
in `A/J`, with scalars restricted along the quotient map. -/
noncomputable def rightIdealLayerRestrictedQuotientImageIso
    (hJI : J ≤ I) :
    cokernel (rightIdealInclusion J I hJI) ≅
      restrictedQuotientImageRightModule J I :=
  ModuleCat.cokernelIsoRangeQuotient
      (rightIdealInclusion J I hJI) ≪≫
    ((Submodule.quotEquivOfEq _ _
        (range_rightIdealInclusion_eq_ker J I hJI)) ≪≫ₗ
      (rightIdealToRestrictedQuotientImage J I).quotKerEquivOfSurjective
        (rightIdealToRestrictedQuotientImage_surjective J I)).toModuleIso


-- @@ L136-136 verbatim
end QuotientSubmoduleEquidistribution.Tsukamoto
