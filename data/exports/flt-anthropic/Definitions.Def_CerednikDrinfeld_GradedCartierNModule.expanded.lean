import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace CerednikDrinfeld


-- @@ L11-11 verbatim
namespace GradedCartierModuleData


-- @@ L13-13 verbatim
variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

-- @@ L14-14 verbatim
variable (D : GradedCartierModuleData p B j)


-- @@ L16-16 verbatim
local notation "𝕎" => WittVector p B

-- @@ L17-17 verbatim
local notation "σ" => (WittVector.frobenius : WittVector p B →+* WittVector p B)


-- @@ L19-19 verbatim
def Sigma (D : GradedCartierModuleData p B j) : Type := D.M


-- @@ L21-21 verbatim
instance : AddCommGroup D.Sigma := inferInstanceAs (AddCommGroup D.M)

-- @@ L22-23 verbatim
instance : Module (WittVector p B) D.Sigma :=
  (Module.compHom D.M (WittVector.frobenius : WittVector p B →+* WittVector p B) :)


-- @@ L25-25 verbatim
def toSigma : D.M ≃+ D.Sigma := AddEquiv.refl _


-- @@ L27-27 verbatim
def ofSigma : D.Sigma ≃+ D.M := AddEquiv.refl _


-- @@ L29-29 verbatim
@[simp] theorem ofSigma_toSigma (m : D.M) : D.ofSigma (D.toSigma m) = m := rfl

-- @@ L30-30 verbatim
@[simp] theorem toSigma_ofSigma (m : D.Sigma) : D.toSigma (D.ofSigma m) = m := rfl


-- @@ L32-33 verbatim
theorem smul_toSigma (w : WittVector p B) (m : D.M) :
    w • D.toSigma m = D.toSigma (WittVector.frobenius w • m) := rfl


-- @@ L35-36 verbatim
theorem ofSigma_smul (w : WittVector p B) (m : D.Sigma) :
    D.ofSigma (w • m) = WittVector.frobenius w • D.ofSigma m := rfl


-- @@ L38-45 verbatim
def nRelMap : D.Sigma →ₗ[WittVector p B] D.M × D.Sigma where
  toFun m := (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
  map_add' m m' := by
    simp only [map_add, map_neg, neg_add, Prod.mk_add_mk]
  map_smul' w m := by
    show (D.verschiebung (D.ofSigma (w • m)), D.toSigma (-D.varpi (D.ofSigma (w • m)))) =
      w • (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
    rw [Prod.smul_mk, ofSigma_smul, D.varpi_smul, D.smul_verschiebung, smul_toSigma, smul_neg]


-- @@ L47-48 verbatim
@[simp] theorem nRelMap_apply (m : D.Sigma) :
    D.nRelMap m = (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m))) := rfl


-- @@ L50-50 verbatim
def nRel : Submodule (WittVector p B) (D.M × D.Sigma) := LinearMap.range D.nRelMap


-- @@ L52-52 verbatim
abbrev NMod : Type := (D.M × D.Sigma) ⧸ D.nRel


-- @@ L54-55 verbatim
def nMk : D.M × D.M →+ D.NMod :=
  (D.nRel.mkQ.toAddMonoidHom).comp (AddMonoidHom.prodMap (AddMonoidHom.id D.M) D.toSigma.toAddMonoidHom)


-- @@ L57-57 verbatim
theorem nMk_apply (m m' : D.M) : D.nMk (m, m') = D.nRel.mkQ (m, D.toSigma m') := rfl


-- @@ L59-62 verbatim
theorem nMk_surjective : Function.Surjective D.nMk := by
  intro z
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nRel.mkQ_surjective z
  exact ⟨(m, D.ofSigma m'), rfl⟩


-- @@ L64-66 verbatim
theorem nMk_verschiebung_neg_varpi (m : D.M) : D.nMk (D.verschiebung m, -D.varpi m) = 0 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨D.toSigma m, rfl⟩


-- @@ L68-69 verbatim
theorem smul_nMk (w : WittVector p B) (m m' : D.M) :
    w • D.nMk (m, m') = D.nMk (w • m, WittVector.frobenius w • m') := rfl


-- @@ L71-82 verbatim
def lambda : D.NMod →ₗ[WittVector p B] D.M :=
  D.nRel.liftQ
    { toFun := fun x => D.varpi x.1 + D.verschiebung (D.ofSigma x.2)
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
      map_smul' := fun w x => by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ofSigma_smul, RingHom.id_apply, smul_add,
          D.smul_verschiebung] }
    (by
      rintro x ⟨m, rfl⟩
      show D.varpi (D.verschiebung (D.ofSigma m)) + D.verschiebung (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m)))) = 0
      rw [ofSigma_toSigma, map_neg, D.varpi_verschiebung, add_neg_cancel])


-- @@ L84-84 verbatim
@[simp] theorem lambda_nMk (m m' : D.M) : D.lambda (D.nMk (m, m')) = D.varpi m + D.verschiebung m' := rfl


-- @@ L86-94 verbatim
def vRange : Submodule (WittVector p B) D.M where
  carrier := Set.range D.verschiebung
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  smul_mem' := by
    rintro w _ ⟨x, rfl⟩
    exact ⟨WittVector.frobenius w • x, (D.smul_verschiebung w x).symm⟩


-- @@ L96-96 verbatim
theorem mem_vRange_iff (x : D.M) : x ∈ D.vRange ↔ ∃ y, D.verschiebung y = x := Iff.rfl


-- @@ L98-98 verbatim
abbrev LieQuot : Type := D.M ⧸ D.vRange


-- @@ L100-105 verbatim
def toLieQuot : D.NMod →ₗ[WittVector p B] D.LieQuot :=
  D.nRel.liftQ (D.vRange.mkQ.comp (LinearMap.fst _ _ _)) (by
    rintro x ⟨m, rfl⟩
    show D.vRange.mkQ (D.verschiebung (D.ofSigma m)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨D.ofSigma m, rfl⟩)


-- @@ L107-107 verbatim
def inrSigma : D.Sigma →ₗ[WittVector p B] D.NMod := D.nRel.mkQ.comp (LinearMap.inr _ _ _)


-- @@ L109-121 verbatim
def nVarpi : D.NMod →ₗ[WittVector p B] D.NMod :=
  D.nRel.mapQ D.nRel
    (LinearMap.prodMap D.varpi
      { toFun := fun m => D.toSigma (D.varpi (D.ofSigma m))
        map_add' := fun x y => by simp only [map_add]
        map_smul' := fun w m => by rw [ofSigma_smul, map_smul, RingHom.id_apply, smul_toSigma] })
    (by
      rintro x ⟨m, rfl⟩
      refine ⟨D.toSigma (D.varpi (D.ofSigma m)), ?_⟩
      show (D.verschiebung (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))),
          D.toSigma (-D.varpi (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))))) =
        (D.varpi (D.verschiebung (D.ofSigma m)), D.toSigma (D.varpi (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
      simp only [ofSigma_toSigma, D.varpi_verschiebung, map_neg])


-- @@ L123-124 verbatim
def nPiece (i : Fin 2) : AddSubgroup D.NMod :=
  (((D.piece i).toAddSubgroup).prod ((D.piece i).toAddSubgroup)).map D.nMk


-- @@ L126-136 verbatim
def nMap {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) : D.NMod →+ D'.NMod :=
  QuotientAddGroup.map D.nRel.toAddSubgroup D'.nRel.toAddSubgroup
    (AddMonoidHom.prodMap f (D'.toSigma.toAddMonoidHom.comp (f.comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    refine ⟨D'.toSigma (f (D.ofSigma m)), ?_⟩
    show (D'.verschiebung (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))),
        D'.toSigma (-D'.varpi (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))))) =
      (f (D.verschiebung (D.ofSigma m)), D'.toSigma (f (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
    simp only [ofSigma_toSigma, hV, map_neg, hPi])


-- @@ L138-141 verbatim
theorem nMap_nMk {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (m m' : D.M) :
    D.nMap D' f hV hPi (D.nMk (m, m')) = D'.nMk (f m, f m') := rfl


-- @@ L143-151 verbatim
def IsBaseChangeAlong' {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧ D'.IsHomogeneousVBasis (fun i => f (γ i)))


-- @@ L153-156 verbatim
structure IsCartierLMap (L : D.M →+ D.NMod) : Prop where
  map_smul : ∀ (w : WittVector p B) (x : D.M), L (w • x) = WittVector.frobenius w • L x
  map_verschiebung : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)
  lambda_comp : ∀ x : D.M, D.lambda (L x) = D.frobenius x


-- @@ L158-165 verbatim
structure IsCanonicalLMap (L : D.M →+ D.NMod) : Prop where
  isCartierLMap : D.IsCartierLMap L
  exists_lift : ∃ (S : Type) (_ : CommRing S) (jS : Zp2 p →+* S) (φ : S →+* B)
    (_ : Function.Surjective φ) (_ : ∀ s : S, (p : S) * s = 0 → s = 0)
    (Dl : GradedCartierModuleData p S jS) (_ : Dl.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : IsBaseChangeAlong' φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (_ : Dl.IsCartierLMap Ll),
    ∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x)


-- @@ L167-167 verbatim
def cartierL (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.M →+ D.NMod := h.choose


-- @@ L169-170 verbatim
theorem cartierL_spec (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.IsCanonicalLMap (D.cartierL h) :=
  h.choose_spec


-- @@ L172-179 verbatim
def phi (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.NMod →+ D.NMod :=
  QuotientAddGroup.lift D.nRel.toAddSubgroup
    (AddMonoidHom.coprod L (D.nMk.comp ((AddMonoidHom.inl D.M D.M).comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    show L (D.verschiebung (D.ofSigma m)) + D.nMk (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))), 0) = 0
    rw [hL, ofSigma_toSigma, ← map_add, Prod.mk_add_mk, add_neg_cancel, add_zero]
    exact map_zero D.nMk)


-- @@ L181-182 verbatim
theorem phi_nMk (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (x x' : D.M) : D.phi L hL (D.nMk (x, x')) = L x + D.nMk (x', 0) := rfl


-- @@ L184-186 verbatim
def eta (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    AddSubgroup D.NMod :=
  (D.phi L hL - AddMonoidHom.id D.NMod).ker


-- @@ L188-191 verbatim
theorem mem_eta_iff (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (z : D.NMod) : z ∈ D.eta L hL ↔ D.phi L hL z = z := by
  rw [eta, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
  rfl


-- @@ L193-195 verbatim
def etaPiece (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (i : Fin 2) : AddSubgroup D.NMod :=
  D.eta L hL ⊓ D.nPiece i


-- @@ L197-199 verbatim
def u (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.eta L hL →+ D.LieQuot :=
  D.toLieQuot.toAddMonoidHom.comp (D.eta L hL).subtype


-- @@ L201-201 verbatim
end GradedCartierModuleData


-- @@ L203-203 verbatim
end CerednikDrinfeld


-- @@ L205-205 verbatim
end
