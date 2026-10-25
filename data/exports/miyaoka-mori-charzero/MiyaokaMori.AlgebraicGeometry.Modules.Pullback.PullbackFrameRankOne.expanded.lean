import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameIsFrame


-- @@ L4-21 verbatim
/-! # The pullback of a frame of a line bundle is a frame

**The pullback of a frame of a line bundle is a frame** (rank-1 case of `isFrameOn_pullback`,
Stacks 01C6/01CR), and **the adjunction unit is linear**: for `f : X ⟶ Y`, `F : Y.Modules`,
`e ∈ Γ(F, V)` a frame of `F` on `V ⊆ Y` (`IsFrame`), the unit section
`unitSec f F e ∈ Γ(f^*F, f⁻¹V)` is a frame of `f^*F` on `f⁻¹V`; and
`unitSec f F (r • m) = f.app V r • unitSec f F m`.

Proof: `IsFrame M U e ↔ IsFrameOn M (fun _ : PUnit => e)` (`isFrameOn_punit_iff`): the frame map
of the singleton family is `r ↦ r () • e|`, so both bijectivity statements are the same up to the
equivalence `(PUnit → R) ≃ R`. Then apply `isFrameOn_pullback` (`PullbackFrameIsFrame.lean`), whose
pulled-back family
`unitFrame' f F V (fun _ => e)` is definitionally `fun _ => unitSec f F e`. Linearity of the unit
section is `Hom.app_smul` for the unit `F ⟶ f_* f^* F`, the `Γ(Y, V)`-action on `Γ(f_* f^*F, V) =
Γ(f^*F, f⁻¹V)` being through `f.app V`.

Used for `O_X(f^*D) ≅ f^*O_Y(D)` (frames `f^*(g_i^{-1})` of `f^*O_Y(D)` on `f^{-1}U_i`).
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 400000


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
open CategoryTheory Opposite TopologicalSpace

-- @@ L29-29 verbatim
open scoped AlgebraicGeometry

-- @@ L30-30 verbatim
open AlgebraicGeometry


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace MiyaokaMori.DualPullback


-- @@ L36-36 verbatim
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)


-- @@ L38-38 verbatim
set_option backward.isDefEq.respectTransparency false


-- @@ L40-40 verbatim
variable {X : Scheme.{u}}


-- @@ L42-46 verbatim
/-- The frame map of a singleton family is `r ↦ r () • e|`. -/
theorem frameMap_punit_apply (M : X.Modules) {U : X.Opens} (e : Γ(M, U)) {W : X.Opens}
    (hW : W ≤ U) (r : PUnit.{u + 1} → Γ(X, W)) :
    frameMap M (fun _ : PUnit.{u + 1} => e) hW r = r PUnit.unit • res M hW e := by
  rw [frameMap_apply, Fintype.sum_unique]


-- @@ L48-65 verbatim
/-- `IsFrame` is `IsFrameOn` for the singleton family. -/
theorem isFrameOn_punit_iff (M : X.Modules) {U : X.Opens} (e : Γ(M, U)) :
    IsFrameOn M (fun _ : PUnit.{u + 1} => e) ↔ Scheme.Modules.IsFrame M U e := by
  have key : ∀ (W : X.Opens) (hW : W ≤ U),
      ⇑(frameMap M (fun _ : PUnit.{u + 1} => e) hW) =
        (fun r : Γ(X, W) => r • Scheme.Modules.res M hW e) ∘
          (Equiv.funUnique PUnit.{u + 1} Γ(X, W)) := by
    intro W hW
    funext r
    exact frameMap_punit_apply M e hW r
  constructor
  · intro h W hW
    have := h W hW
    rw [key] at this
    exact (Function.Bijective.of_comp_iff _ (Equiv.funUnique _ _).bijective).mp this
  · intro h W hW
    rw [key]
    exact (h W hW).comp (Equiv.funUnique _ _).bijective


-- @@ L67-67 verbatim
variable {Y : Scheme.{u}}


-- @@ L69-73 verbatim
/-- **The pullback of a frame is a frame** (rank 1): `unit(e)` is a frame of `f^*F` on `f⁻¹V`. -/
theorem isFrame_unitSec_pullback (f : X ⟶ Y) (F : Y.Modules) {V : Y.Opens} {e : Γ(F, V)}
    (he : Scheme.Modules.IsFrame F V e) :
    Scheme.Modules.IsFrame ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) (unitSec f F e) :=
  (isFrameOn_punit_iff _ _).mp (isFrameOn_pullback f F V ((isFrameOn_punit_iff F e).mpr he))


-- @@ L75-78 verbatim
/-- The unit section is linear: `unit(r • m) = f^♯(r) • unit(m)`. -/
theorem unitSec_smul (f : X ⟶ Y) (F : Y.Modules) {Z : Y.Opens} (r : Γ(Y, Z)) (m : Γ(F, Z)) :
    unitSec f F (r • m) = f.app Z r • unitSec f F m :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) r m


-- @@ L80-80 verbatim
end MiyaokaMori.DualPullback


-- @@ L82-82 verbatim
end
