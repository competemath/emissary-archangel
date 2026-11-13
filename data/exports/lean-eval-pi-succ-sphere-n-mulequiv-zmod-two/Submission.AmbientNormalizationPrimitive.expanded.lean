import Mathlib
import Submission.AmbientIsotopyCobordism


-- @@ L4-20 verbatim
/-!
# Relative composition of ambient normalization moves

Normalizing a finite framed fiber component-by-component requires two facts
which are not contained in the one-isotopy sweep construction:

* ambient isotopies can be composed while remaining a smooth ambient isotopy;
* an isotopy which fixes an already-normalized set sweeps a literal product
  over that set.

The final construction in this file is the normalization primitive used by a
per-orbit induction.  It composes, as actual signed cobordisms, an ambient
isotopy of the embedded fiber, a common-fiber homotopy of its defining map
(the frame-normalization step), and interpolation to any target label with the
same sign pattern.  No cobordism-existence field or additional geometric
axiom is introduced.
-/


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function Metric

-- @@ L25-25 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L33-33 verbatim
namespace SmoothAmbientIsotopy


-- @@ L35-35 verbatim
/-! ## Identity and pointwise composition -/


-- @@ L37-57 verbatim
/-- The constant identity ambient isotopy. -/
def refl (n : ℕ) : SmoothAmbientIsotopy n where
  forward _ x := x
  inverse _ x := x
  forward_smooth := contDiff_snd
  inverse_smooth := contDiff_snd
  forward_zero := rfl
  left_inv := by
    intro _ _ x
    rfl
  right_inv := by
    intro _ _ x
    rfl
  inverse_fderiv_surjective := by
    intro _ _ x
    have hfd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y) x =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
      (hasFDerivAt_id x).fderiv
    rw [hfd]
    intro y
    exact ⟨y, rfl⟩


-- @@ L59-61 verbatim
@[simp] theorem refl_forward (s : ℝ) (x : E) :
    (refl n).forward s x = x :=
  rfl


-- @@ L63-65 verbatim
@[simp] theorem refl_inverse (s : ℝ) (x : E) :
    (refl n).inverse s x = x :=
  rfl


-- @@ L67-103 verbatim
/-- Pointwise composition of ambient isotopies.

At each time, `A.followedBy B` first applies `A` and then `B`.  Its inverse therefore
applies the inverses in the opposite order.  This operation is particularly
useful for combining finitely many relative, component-supported moves: their
endpoint diffeomorphism is the desired composition without inserting any new
regularity hypothesis. -/
def followedBy (A B : SmoothAmbientIsotopy n) : SmoothAmbientIsotopy n where
  forward s x := B.forward s (A.forward s x)
  inverse s x := A.inverse s (B.inverse s x)
  forward_smooth := B.forward_smooth.comp
    (contDiff_fst.prodMk A.forward_smooth)
  inverse_smooth := A.inverse_smooth.comp
    (contDiff_fst.prodMk B.inverse_smooth)
  forward_zero := by
    funext x
    rw [A.forward_zero, B.forward_zero]
    rfl
  left_inv := by
    intro s hs x
    change A.inverse s (B.inverse s (B.forward s (A.forward s x))) = x
    rw [B.left_inv s hs, A.left_inv s hs]
  right_inv := by
    intro s hs x
    change B.forward s (A.forward s (A.inverse s (B.inverse s x))) = x
    rw [A.right_inv s hs, B.right_inv s hs]
  inverse_fderiv_surjective := by
    intro s hs x
    have hchain :
        fderiv ℝ (fun y : E => A.inverse s (B.inverse s y)) x =
          (fderiv ℝ (A.inverse s) (B.inverse s x)).comp
            (fderiv ℝ (B.inverse s) x) := by
      exact (((A.contDiff_inverse_slice s).differentiable (by simp) _).hasFDerivAt.comp x
        ((B.contDiff_inverse_slice s).differentiable (by simp) x).hasFDerivAt).fderiv
    rw [hchain]
    exact (A.inverse_fderiv_surjective s hs (B.inverse s x)).comp
      (B.inverse_fderiv_surjective s hs x)


-- @@ L105-107 verbatim
@[simp] theorem followedBy_forward (A B : SmoothAmbientIsotopy n) (s : ℝ) (x : E) :
    (A.followedBy B).forward s x = B.forward s (A.forward s x) :=
  rfl


-- @@ L109-111 verbatim
@[simp] theorem followedBy_inverse (A B : SmoothAmbientIsotopy n) (s : ℝ) (x : E) :
    (A.followedBy B).inverse s x = A.inverse s (B.inverse s x) :=
  rfl


-- @@ L113-117 verbatim
/-- Finite pointwise composition, in list order.  Thus `[A, B]` has endpoint
map `B₁ ∘ A₁`. -/
def composeList : List (SmoothAmbientIsotopy n) → SmoothAmbientIsotopy n
  | [] => refl n
  | A :: tail => A.followedBy (composeList tail)


-- @@ L119-121 verbatim
@[simp] theorem composeList_nil :
    composeList ([] : List (SmoothAmbientIsotopy n)) = refl n :=
  rfl


-- @@ L123-126 verbatim
@[simp] theorem composeList_cons (A : SmoothAmbientIsotopy n)
    (tail : List (SmoothAmbientIsotopy n)) :
    composeList (A :: tail) = A.followedBy (composeList tail) :=
  rfl


-- @@ L128-128 verbatim
/-! ## Relative fixed sets -/


-- @@ L130-133 verbatim
/-- An ambient isotopy is stationary on `K` throughout the geometric time
interval. -/
def FixedOn (A : SmoothAmbientIsotopy n) (K : Set E) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, A.forward s x = x


-- @@ L135-137 verbatim
theorem fixedOn_refl (K : Set E) : (refl n).FixedOn K := by
  intro s hs x hx
  rfl


-- @@ L139-143 verbatim
/-- Pointwise composition preserves every common relative fixed set. -/
theorem FixedOn.followedBy {A B : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) (hB : B.FixedOn K) : (A.followedBy B).FixedOn K := by
  intro s hs x hx
  rw [followedBy_forward, hA s hs x hx, hB s hs x hx]


-- @@ L145-149 verbatim
/-- Restricting the set of stationary points preserves relative fixedness. -/
theorem FixedOn.mono {A : SmoothAmbientIsotopy n} {K L : Set E}
    (hA : A.FixedOn K) (hLK : L ⊆ K) : A.FixedOn L := by
  intro s hs x hx
  exact hA s hs x (hLK hx)


-- @@ L151-162 verbatim
/-- A finite family of moves fixing the same set can be composed into one
ambient isotopy which still fixes that set. -/
theorem fixedOn_composeList {K : Set E} :
    ∀ (moves : List (SmoothAmbientIsotopy n)),
      (∀ A ∈ moves, A.FixedOn K) → (composeList moves).FixedOn K
  | [], _ => fixedOn_refl K
  | A :: tail, h => by
      apply FixedOn.followedBy
      · exact h A (by simp)
      · apply fixedOn_composeList tail
        intro B hB
        exact h B (by simp [hB])


-- @@ L164-170 verbatim
/-- The inverse of a relative ambient isotopy fixes the same set. -/
theorem FixedOn.inverse_eq {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {x : E} (hx : x ∈ K) : A.inverse s x = x := by
  have hleft := A.left_inv s hs x
  rw [hA s hs x hx] at hleft
  exact hleft


-- @@ L172-179 verbatim
/-- Along a relative fixed set the inverse track used by the swept
cobordism is literally the spatial projection. -/
theorem FixedOn.inverseTrack_eq {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hv : initCLM (n + 1) v ∈ K) :
    A.inverseTrack v = initCLM (n + 1) v := by
  exact hA.inverse_eq
    ⟨normRamp_nonneg (vertC v), normRamp_le_one (vertC v)⟩ hv


-- @@ L181-186 verbatim
/-- The transported endpoint defining map is unchanged on a relative fixed
set. -/
theorem FixedOn.pullback_g_eq {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) (X : FramedLevelSet n) {x : E} (hx : x ∈ K) :
    (A.pullback X).g x = X.g x := by
  rw [A.pullback_g, hA.inverse_eq ⟨zero_le_one, le_rfl⟩ hx]


-- @@ L188-193 verbatim
/-- The transported endpoint label is unchanged on a relative fixed set. -/
theorem FixedOn.pullbackSign_eq {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) {X : FramedLevelSet n} (S : FiberSign X)
    {x : E} (hx : x ∈ K) :
    A.pullbackSign S x = S x := by
  rw [A.pullbackSign_apply, hA.inverse_eq ⟨zero_le_one, le_rfl⟩ hx]


-- @@ L195-203 verbatim
/-- The swept defining map is a literal product over every relative fixed
point, at every (not necessarily collar) time. -/
theorem FixedOn.cobordism_product {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) (X : FramedLevelSet n) {x : E} (hx : x ∈ K)
    (t : ℝ) :
    (A.cobordism X).G (spaceTime x t) = X.g x := by
  change X.g (A.inverseTrack (spaceTime x t)) = X.g x
  rw [hA.inverseTrack_eq (by rwa [initCLM_spaceTime])]
  rw [initCLM_spaceTime]


-- @@ L205-213 verbatim
/-- The swept sign is likewise a literal product over every relative fixed
point. -/
theorem FixedOn.signedCobordism_product {A : SmoothAmbientIsotopy n}
    {K : Set E} (hA : A.FixedOn K) {X : FramedLevelSet n} (S : FiberSign X)
    {x : E} (hx : x ∈ K) (t : ℝ) :
    A.signedCobordism S (spaceTime x t) = S x := by
  change S (A.inverseTrack (spaceTime x t)) = S x
  rw [hA.inverseTrack_eq (by rwa [initCLM_spaceTime])]
  rw [initCLM_spaceTime]


-- @@ L215-215 verbatim
/-! ## Ambient move, frame normalization, and label normalization -/


-- @@ L217-235 verbatim
/-- The concrete three-stage primitive for one orbit-normalization step.

First the ambient isotopy moves the embedded fiber.  Next `D` changes only
the defining equations on that moved fiber, which is exactly the normal-frame
homotopy.  Finally the sign label is interpolated to the chosen target label.
The sole sign hypothesis is the necessary pointwise equality of sign patterns
on the target fiber. -/
def signedNormalizationCobordism
    (A : SmoothAmbientIsotopy n) {X Y : FramedLevelSet n}
    (D : DefiningMapHomotopy (A.pullback X) Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < (A.pullbackSign S).restrict D.fiber_subset x ↔ 0 < T x)) :
    SignedFramedLevelCobordism S T :=
  SignedFramedLevelCobordism.trans (A.signedCobordism S)
    (SignedFramedLevelCobordism.trans
      (D.signedCobordism (A.pullbackSign S))
      (signInterpolationCobordism
        ((A.pullbackSign S).restrict D.fiber_subset) T hpos))


-- @@ L237-246 verbatim
/-- Existence form of `signedNormalizationCobordism`, ready to compose in the
`ConfigurationReductionKit.configure` induction. -/
theorem nonempty_signedNormalizationCobordism
    (A : SmoothAmbientIsotopy n) {X Y : FramedLevelSet n}
    (D : DefiningMapHomotopy (A.pullback X) Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < (A.pullbackSign S).restrict D.fiber_subset x ↔ 0 < T x)) :
    Nonempty (SignedFramedLevelCobordism S T) :=
  ⟨signedNormalizationCobordism A D S T hpos⟩


-- @@ L248-248 verbatim
end SmoothAmbientIsotopy


-- @@ L250-250 verbatim
end Submission
