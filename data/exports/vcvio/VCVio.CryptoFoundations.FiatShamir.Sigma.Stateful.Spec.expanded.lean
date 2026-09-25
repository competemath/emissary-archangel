/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.SimpAttr
public import VCVio.OracleComp.OracleSpec
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating


-- @@ L13-23 verbatim
/-!
# Oracle interfaces and plain states for the stateful Fiat-Shamir CMA proof

This file contains the oracle interfaces and direct product-state shapes used
by the `QueryImpl.Stateful` Fiat-Shamir CMA games. The games store their private
data in ordinary product types.

The `fs_simp` simp attribute used to tag handler definitions, frames, lenses,
and adversary wrappers throughout the stateful FS-CMA development is declared
in `Stateful/SimpAttr.lean` and imported above.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open OracleSpec


-- @@ L29-29 verbatim
namespace FiatShamir.Stateful


-- @@ L31-31 verbatim
/-! ## Oracle specs -/


-- @@ L33-40 verbatim
/-- Named query constructors for the source CMA adversary interface. -/
inductive CmaSourceQuery (M Commit : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Signing query. -/
  | sign (m : M)


-- @@ L42-51 verbatim
/-- Named query constructors for the CMA adversary's oracle view. -/
inductive CmaQuery (M Commit : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Signing query. -/
  | sign (m : M)
  /-- Public-key query. -/
  | pk


-- @@ L53-61 verbatim
/-- Named query constructors for the public, non-signing portion of the CMA
interface. -/
inductive CmaPublicQuery (M Commit : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Public-key query. -/
  | pk


-- @@ L63-73 verbatim
/-- Named query constructors for the NMA interface used internally by the
CMA-to-NMA reduction. -/
inductive NmaQuery (M Commit Chal : Type) where
  /-- Uniform sampling query. -/
  | unif (n : ℕ)
  /-- Random-oracle query. -/
  | ro (mc : M × Commit)
  /-- Public-key query. -/
  | pk
  /-- Programmable-random-oracle query. -/
  | prog (mch : M × Commit × Chal)


-- @@ L75-77 expanded
/-- Random-oracle interface for the Fiat-Shamir transform. -/
@[reducible]
def roSpec (M Commit Chal : Type) : OracleSpec (M × Commit) :=
  OracleSpec.ofFn (ι := (M × Commit)) (fun _ => Chal)


-- @@ L79-81 expanded
/-- Signing-oracle interface presented to the CMA adversary. -/
@[reducible]
def signSpec (M Commit Resp : Type) : OracleSpec M :=
  OracleSpec.ofFn (ι := M) (fun _ => (Commit × Resp))


-- @@ L83-86 expanded
/-- Public-key oracle interface: a single `GetPK` query returning the
challenger's public key. -/
@[reducible]
def pkSpec (Stmt : Type) : OracleSpec Unit :=
  OracleSpec.ofFn (ι := Unit) (fun _ => Stmt)


-- @@ L88-90 expanded
/-- Programming interface for the programmable random oracle. -/
@[reducible]
def progSpec (M Commit Chal : Type) : OracleSpec (M × Commit × Chal) :=
  OracleSpec.ofFn (ι := (M × Commit × Chal)) (fun _ => Unit)


-- @@ L92-98 verbatim
/-- Source CMA adversary interface: uniform sampling, RO, and signing. -/
@[reducible] def cmaSourceSpec (M Commit Chal Resp : Type) :
    OracleSpec (CmaSourceQuery M Commit) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .sign _ => Commit × Resp


-- @@ L100-108 verbatim
/-- The CMA adversary's complete oracle view: uniform sampling, RO, signing,
and public-key oracles. -/
@[reducible] def cmaSpec (M Commit Chal Resp Stmt : Type) :
    OracleSpec (CmaQuery M Commit) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .sign _ => Commit × Resp
    | .pk => Stmt


-- @@ L110-113 verbatim
instance {M Commit Chal Resp Stmt : Type}
    [Fintype Chal] [Fintype Commit] [Fintype Resp] [Fintype Stmt] :
    (cmaSpec M Commit Chal Resp Stmt).Fintype where
  fintypeB q := by cases q <;> dsimp [cmaSpec] <;> infer_instance


-- @@ L115-118 verbatim
instance {M Commit Chal Resp Stmt : Type}
    [Inhabited Chal] [Inhabited Commit] [Inhabited Resp] [Inhabited Stmt] :
    (cmaSpec M Commit Chal Resp Stmt).Inhabited where
  inhabitedB q := by cases q <;> dsimp [cmaSpec] <;> infer_instance


-- @@ L120-126 verbatim
/-- The non-signing portion of the CMA adversary's oracle view. -/
@[reducible] def cmaPublicSpec (M Commit Chal Stmt : Type) :
    OracleSpec (CmaPublicQuery M Commit) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .pk => Stmt


-- @@ L128-136 verbatim
/-- The NMA-game oracle interface used internally by the CMA-to-NMA reduction.
Includes uniform sampling, RO, programmable RO, and public-key queries. -/
@[reducible] def nmaSpec (M Commit Chal Stmt : Type) :
    OracleSpec (NmaQuery M Commit Chal) :=
  OracleSpec.ofFn fun
    | .unif n => Fin (n + 1)
    | .ro _ => Chal
    | .pk => Stmt
    | .prog _ => Unit


-- @@ L138-164 verbatim
/-- Route named CMA queries to the public-forwarding component or the signing
component of the CMA-to-NMA reduction. -/
def cmaRoute (M Commit Chal Resp Stmt : Type) :
    QueryImpl.Stateful.ExportRouteEquiv
      (cmaSpec M Commit Chal Resp Stmt)
      (cmaPublicSpec M Commit Chal Stmt)
      (signSpec M Commit Resp) where
  route
    | .unif n => .inl ⟨.unif n, Equiv.refl _⟩
    | .ro mc => .inl ⟨.ro mc, Equiv.refl _⟩
    | .sign m => .inr ⟨m, Equiv.refl _⟩
    | .pk => .inl ⟨.pk, Equiv.refl _⟩
  targetEquiv := {
    toFun
      | .unif n => Sum.inl (CmaPublicQuery.unif n)
      | .ro mc => Sum.inl (CmaPublicQuery.ro mc)
      | .sign m => Sum.inr m
      | .pk => Sum.inl CmaPublicQuery.pk
    invFun
      | Sum.inl (CmaPublicQuery.unif n) => CmaQuery.unif n
      | Sum.inl (CmaPublicQuery.ro mc) => CmaQuery.ro mc
      | Sum.inl CmaPublicQuery.pk => CmaQuery.pk
      | Sum.inr m => CmaQuery.sign m
    left_inv := fun t => by cases t <;> rfl
    right_inv := fun t => by rcases t with (_ | _) | _ <;> rfl
  }
  target_eq := fun t => by rcases t with (_ | _) | _ <;> rfl


-- @@ L166-171 expanded
instance subSpec_unif_nmaSpec (M Commit Chal Stmt : Type) :
    SubSpec unifSpec (nmaSpec M Commit Chal Stmt)
    where
  monadLift q := ⟨.unif q.input, q.cont⟩
  onQuery n := .unif n
  onResponse _ := id
  liftM_eq_lift _ := rfl


-- @@ L173-175 expanded
instance lawfulSubSpec_unif_nmaSpec (M Commit Chal Stmt : Type) :
    LawfulSubSpec unifSpec (nmaSpec M Commit Chal Stmt) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L177-181 expanded
instance subSpec_unif_cmaSpec (M Commit Chal Resp Stmt : Type) :
    SubSpec unifSpec (cmaSpec M Commit Chal Resp Stmt)
    where
  monadLift q := ⟨.unif q.input, q.cont⟩
  onQuery n := .unif n
  onResponse _ := id


-- @@ L183-185 expanded
instance lawfulSubSpec_unif_cmaSpec (M Commit Chal Resp Stmt : Type) :
    LawfulSubSpec unifSpec (cmaSpec M Commit Chal Resp Stmt) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L187-191 expanded
instance subSpec_ro_cmaSpec (M Commit Chal Resp Stmt : Type) :
    SubSpec (roSpec M Commit Chal) (cmaSpec M Commit Chal Resp Stmt)
    where
  monadLift q := ⟨.ro q.input, q.cont⟩
  onQuery mc := .ro mc
  onResponse _ := id


-- @@ L193-195 expanded
instance lawfulSubSpec_ro_cmaSpec (M Commit Chal Resp Stmt : Type) :
    LawfulSubSpec (roSpec M Commit Chal) (cmaSpec M Commit Chal Resp Stmt) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L197-201 expanded
instance subSpec_sign_cmaSpec (M Commit Chal Resp Stmt : Type) :
    SubSpec (signSpec M Commit Resp) (cmaSpec M Commit Chal Resp Stmt)
    where
  monadLift q := ⟨.sign q.input, q.cont⟩
  onQuery m := .sign m
  onResponse _ := id


-- @@ L203-205 expanded
instance lawfulSubSpec_sign_cmaSpec (M Commit Chal Resp Stmt : Type) :
    LawfulSubSpec (signSpec M Commit Resp) (cmaSpec M Commit Chal Resp Stmt) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L207-212 expanded
instance subSpec_pk_cmaSpec (M Commit Chal Resp Stmt : Type) :
    SubSpec (pkSpec Stmt) (cmaSpec M Commit Chal Resp Stmt)
    where
  monadLift
    | ⟨(), f⟩ => ⟨.pk, f⟩
  onQuery _ := .pk
  onResponse _ := id


-- @@ L214-216 expanded
instance lawfulSubSpec_pk_cmaSpec (M Commit Chal Resp Stmt : Type) :
    LawfulSubSpec (pkSpec Stmt) (cmaSpec M Commit Chal Resp Stmt) where
  onResponse_bijective _ := Function.bijective_id


-- @@ L218-232 expanded
/-- The Fiat-Shamir public random-oracle interface embeds into the named CMA
interface by routing uniform and random-oracle queries to their named
constructors. -/
instance subSpec_fsRo_cmaSpec (M Commit Chal Resp Stmt : Type) :
    SubSpec (unifSpec + roSpec M Commit Chal) (cmaSpec M Commit Chal Resp Stmt)
    where
  monadLift
    | ⟨.inl n, f⟩ => ⟨.unif n, f⟩
    | ⟨.inr mc, f⟩ => ⟨.ro mc, f⟩
  onQuery
    | .inl n => .unif n
    | .inr mc => .ro mc
  onResponse
    | .inl _ => id
    | .inr _ => id
  liftM_eq_lift q := by rcases q with ⟨_ | _, _⟩ <;> rfl


-- @@ L234-238 expanded
instance lawfulSubSpec_fsRo_cmaSpec (M Commit Chal Resp Stmt : Type) :
    LawfulSubSpec (unifSpec + roSpec M Commit Chal) (cmaSpec M Commit Chal Resp Stmt) where
  onResponse_bijective
    | .inl _ => Function.bijective_id
    | .inr _ => Function.bijective_id


-- @@ L240-256 expanded
/-- The source CMA adversary interface embeds into the named CMA interface. -/
instance subSpec_sourceCma_cmaSpec (M Commit Chal Resp Stmt : Type) :
    SubSpec (unifSpec + roSpec M Commit Chal + signSpec M Commit Resp)
      (cmaSpec M Commit Chal Resp Stmt)
    where
  monadLift
    | ⟨.inl (.inl n), f⟩ => ⟨.unif n, f⟩
    | ⟨.inl (.inr mc), f⟩ => ⟨.ro mc, f⟩
    | ⟨.inr m, f⟩ => ⟨.sign m, f⟩
  onQuery
    | .inl (.inl n) => .unif n
    | .inl (.inr mc) => .ro mc
    | .inr m => .sign m
  onResponse
    | .inl (.inl _) => id
    | .inl (.inr _) => id
    | .inr _ => id
  liftM_eq_lift q := by rcases q with ⟨(_ | _) | _, _⟩ <;> rfl


-- @@ L258-264 expanded
instance lawfulSubSpec_sourceCma_cmaSpec (M Commit Chal Resp Stmt : Type) :
    LawfulSubSpec (unifSpec + roSpec M Commit Chal + signSpec M Commit Resp)
      (cmaSpec M Commit Chal Resp Stmt)
    where
  onResponse_bijective
    | .inl (.inl _) => Function.bijective_id
    | .inl (.inr _) => Function.bijective_id
    | .inr _ => Function.bijective_id


-- @@ L266-266 verbatim
/-! ## Plain state shapes -/


-- @@ L268-270 verbatim
/-- Random-oracle cache state. -/
abbrev RoCache (M Commit Chal : Type) :=
  (roSpec M Commit Chal).QueryCache


-- @@ L272-274 verbatim
/-- Outer CMA-to-NMA state: the signed-message log. -/
abbrev OuterState (M : Type) :=
  List M


-- @@ L276-278 verbatim
/-- Inner NMA state: RO cache, optional keypair, and bad flag. -/
abbrev NmaState (M Commit Chal Stmt Wit : Type) :=
  RoCache M Commit Chal × Option (Stmt × Wit) × Bool


-- @@ L280-282 verbatim
/-- Direct CMA state without the bad flag: signed log, RO cache, keypair. -/
abbrev CmaData (M Commit Chal Stmt Wit : Type) :=
  OuterState M × RoCache M Commit Chal × Option (Stmt × Wit)


-- @@ L284-286 verbatim
/-- Direct CMA state with the bad flag as the final component. -/
abbrev CmaState (M Commit Chal Stmt Wit : Type) :=
  CmaData M Commit Chal Stmt Wit × Bool


-- @@ L288-291 verbatim
/-- Initial NMA state: empty RO cache, no keypair, bad unset. -/
@[reducible] def nmaInit (M Commit Chal Stmt Wit : Type) :
    NmaState M Commit Chal Stmt Wit :=
  (∅, none, false)


-- @@ L293-296 verbatim
/-- Initial CMA state: empty signed log, empty RO cache, no keypair, bad unset. -/
@[reducible] def cmaInit (M Commit Chal Stmt Wit : Type) :
    CmaState M Commit Chal Stmt Wit :=
  (([], ∅, none), false)


-- @@ L298-298 verbatim
/-! ## Frame for linking CMA-to-NMA over direct CMA state -/


-- @@ L300-304 verbatim
/-- Lens selecting the signed-message log from direct CMA state. -/
@[fs_simp] def cmaOuterLens (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State (CmaState M Commit Chal Stmt Wit) (OuterState M) :=
  PFunctor.Lens.State.mk (fun s => s.1.1)
    (fun log s => ((log, s.1.2.1, s.1.2.2), s.2))


-- @@ L306-311 verbatim
/-- Lens selecting the NMA state from direct CMA state. -/
@[fs_simp] def cmaNmaLens (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State (CmaState M Commit Chal Stmt Wit)
      (NmaState M Commit Chal Stmt Wit) :=
  PFunctor.Lens.State.mk (fun s => (s.1.2.1, s.1.2.2, s.2))
    (fun inner s => ((s.1.1, inner.1, inner.2.1), inner.2.2))


-- @@ L313-318 verbatim
instance cmaOuterLens_isVeryWellBehaved (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State.IsVeryWellBehaved
      (cmaOuterLens M Commit Chal Stmt Wit) where
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl


-- @@ L320-325 verbatim
instance cmaNmaLens_isVeryWellBehaved (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State.IsVeryWellBehaved
      (cmaNmaLens M Commit Chal Stmt Wit) where
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl


-- @@ L327-333 verbatim
instance cmaOuterLens_cmaNmaLens_isSeparated (M Commit Chal Stmt Wit : Type) :
    PFunctor.Lens.State.IsSeparated
      (cmaOuterLens M Commit Chal Stmt Wit)
      (cmaNmaLens M Commit Chal Stmt Wit) where
  left_get_put_right _ _ := rfl
  right_get_put_left _ _ := rfl
  put_comm _ _ _ := rfl


-- @@ L335-340 verbatim
/-- The direct CMA frame used by `cmaToNma.linkWith nma`. -/
@[fs_simp] def cmaFrame (M Commit Chal Stmt Wit : Type) :
    QueryImpl.Stateful.Frame (CmaState M Commit Chal Stmt Wit)
      (OuterState M) (NmaState M Commit Chal Stmt Wit) where
  left := cmaOuterLens M Commit Chal Stmt Wit
  right := cmaNmaLens M Commit Chal Stmt Wit


-- @@ L342-342 verbatim
/-! ## Frame for routing the CMA-to-NMA reduction -/


-- @@ L344-346 verbatim
/-- Trivial lens into a `PUnit` component. -/
@[fs_simp] def unitLens (σ : Type) : PFunctor.Lens.State σ PUnit :=
  PFunctor.Lens.State.mk (fun _ => PUnit.unit) (fun _ s => s)


-- @@ L348-352 verbatim
instance unitLens_isVeryWellBehaved (σ : Type) :
    PFunctor.Lens.State.IsVeryWellBehaved (unitLens σ) where
  get_put _ _ := rfl
  put_get _ := rfl
  put_put _ _ _ := rfl


-- @@ L354-358 verbatim
instance unitLens_id_isSeparated (σ : Type) :
    PFunctor.Lens.State.IsSeparated (unitLens σ) (PFunctor.Lens.State.id σ) where
  left_get_put_right _ _ := rfl
  right_get_put_left _ _ := rfl
  put_comm _ _ _ := rfl


-- @@ L360-365 verbatim
/-- Frame used to compose the stateless forwarding part of `cmaToNma` with the
stateful signing simulator while keeping only the signing log as state. -/
@[fs_simp] def cmaToNmaFrame (M : Type) :
    QueryImpl.Stateful.Frame (OuterState M) PUnit (OuterState M) where
  left := unitLens (OuterState M)
  right := PFunctor.Lens.State.id (OuterState M)


-- @@ L367-367 verbatim
end FiatShamir.Stateful
