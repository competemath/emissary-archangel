import MiyaokaMori.Prelude


-- @@ L3-19 verbatim
/-! # Pushforward along the inverse of an isomorphism is pullback

For an isomorphism of schemes `e : Z ≅ X`, pushforward and pullback of sheaves of modules are
interchanged: `(pushforward e.inv) ≅ (pullback e.hom)` as functors `X.Modules ⥤ Z.Modules`.

Proof: `Scheme.Modules.pullback` is a pseudofunctor (`pullbackComp`, `pullbackCongr`,
`pullbackId`), so `e.inv^* ⋙ e.hom^* ≅ (e.hom ≫ e.inv)^* = (𝟙 Z)^* ≅ 𝟭` and
`e.hom^* ⋙ e.inv^* ≅ 𝟭`; thus `e.inv^* : Z.Modules ⥤ X.Modules` and `e.hom^*` form an equivalence,
and in particular `e.hom^*` is right adjoint to `e.inv^*`. Mathlib also provides the adjunction
`e.inv^* ⊣ (e.inv)_*` (`pullbackPushforwardAdjunction`). Right adjoints are unique
(`Adjunction.rightAdjointUniq`), so `(e.inv)_* ≅ e.hom^*`.

References: Stacks 03DT (uniqueness of adjoints); Mathlib
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`. Used to transport the cohomology comparison for
closed immersions (Stacks 02UV) along the isomorphism `e.inv`, replacing `(e.inv)_* N` by
`e.hom^* N`.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 400000


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L27-27 verbatim
open scoped AlgebraicGeometry


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L33-33 verbatim
variable {Z X : AlgebraicGeometry.Scheme.{u}}


-- @@ L35-40 verbatim
/-- An isomorphism of schemes `e : Z ≅ X` induces an equivalence `Z.Modules ≌ X.Modules` with
functor `e.inv^*` and inverse `e.hom^*`. -/
def pullbackEquivalenceOfIso (e : Z ≅ X) : Z.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (pullback e.inv) (pullback e.hom)
    (pullbackComp e.hom e.inv ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId Z).symm
    (pullbackComp e.inv e.hom ≪≫ pullbackCongr e.inv_hom_id ≪≫ pullbackId X)


-- @@ L42-46 verbatim
/-- For an isomorphism of schemes `e : Z ≅ X`, the pushforward `(e.inv)_*` and the pullback
`e.hom^*` are naturally isomorphic (uniqueness of right adjoints). -/
def pushforwardInvIsoPullback (e : Z ≅ X) : pushforward e.inv ≅ pullback e.hom :=
  Adjunction.rightAdjointUniq (pullbackPushforwardAdjunction e.inv)
    (pullbackEquivalenceOfIso e).toAdjunction


-- @@ L48-48 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L50-50 verbatim
end
