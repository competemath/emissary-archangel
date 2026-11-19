/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenPortalJoinLayer
import Formalisation.HansenCograph.HansenFullFlagJoinBound
import Formalisation.HansenCograph.CographThreeDBound


-- @@ L10-17 verbatim
/-!
# Complete Hansen graphs have constant portal polynomial

The one-vertex portal layers are first transported to the computable square
model.  The exact join convolution then proves, by a coupled complete/edgeless
cotree induction, that the portal polynomial of a complete cotree evaluation
is constant.
-/


-- @@ L19-19 verbatim
open Set SimpleGraph


-- @@ L21-21 verbatim
namespace HansenCograph


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
namespace SingletonFace


-- @@ L27-32 verbatim
/-- Computable order comparison in the dual singleton face lattice. -/
instance instDecidableLEDualClosed : DecidableLE (OrderDual Closed) := by
  intro F K
  change Decidable
    ((show Closed from K).1 ⊆ (show Closed from F).1)
  infer_instance


-- @@ L34-39 verbatim
/-- Covers are decidable in the finite dual singleton face lattice. -/
instance instDecidableCovByDualClosed :
    DecidableRel (fun F K : OrderDual Closed => F ⋖ K) := by
  intro F K
  unfold CovBy
  infer_instance


-- @@ L41-43 verbatim
/-- Rooted positive faces in the order-dual computable singleton model. -/
abbrev DualRootedPos :=
  {C : OrderDual Closed // IsRootedPos C}


-- @@ L45-47 verbatim
/-- Neutral-or-empty faces in the order-dual computable singleton model. -/
abbrev DualNeutralOrEmpty :=
  {C : OrderDual Closed // IsNeutralOrEmpty C}


-- @@ L49-51 verbatim
/-- Forgetting the order-dual tag identifies the two rooted-positive
singleton presentations. -/
def dualRootedPosEquiv : DualRootedPos ≃ RootedPos := Equiv.refl _


-- @@ L53-56 verbatim
/-- Forgetting the order-dual tag identifies the two neutral singleton
presentations. -/
def dualNeutralOrEmptyEquiv : DualNeutralOrEmpty ≃ NeutralOrEmpty :=
  Equiv.refl _


-- @@ L58-60 verbatim
/-- Explicit computable enumeration of dual rooted-positive faces. -/
instance instFintypeDualRootedPos : Fintype DualRootedPos :=
  Fintype.ofEquiv RootedPos dualRootedPosEquiv.symm


-- @@ L62-64 verbatim
/-- Explicit decidable equality on dual rooted-positive faces. -/
instance instDecidableEqDualRootedPos : DecidableEq DualRootedPos :=
  dualRootedPosEquiv.decidableEq


-- @@ L66-68 verbatim
/-- Explicit computable enumeration of dual neutral-or-empty faces. -/
instance instFintypeDualNeutralOrEmpty : Fintype DualNeutralOrEmpty :=
  Fintype.ofEquiv NeutralOrEmpty dualNeutralOrEmptyEquiv.symm


-- @@ L70-73 verbatim
/-- Explicit decidable equality on dual neutral-or-empty faces. -/
instance instDecidableEqDualNeutralOrEmpty :
    DecidableEq DualNeutralOrEmpty :=
  dualNeutralOrEmptyEquiv.decidableEq


-- @@ L75-78 verbatim
/-- Computable order comparison on the rooted-positive subtype. -/
instance instDecidableLEDualRootedPos : DecidableLE DualRootedPos := by
  intro F K
  exact instDecidableLEDualClosed F.1 K.1


-- @@ L80-84 verbatim
/-- A computable finite presentation of every rooted upper interval. -/
instance instFintypeIciDualRootedPos (F : DualRootedPos) :
    Fintype (Set.Ici F) := by
  change Fintype {K : DualRootedPos // F ≤ K}
  infer_instance


-- @@ L86-90 verbatim
/-- A computable finite presentation of every neutral lower interval. -/
instance instFintypeIicDualClosed (F : OrderDual Closed) :
    Fintype (Set.Iic F) := by
  change Fintype {K : OrderDual Closed // K ≤ F}
  infer_instance


-- @@ L92-95 verbatim
/-- Positive portals in the order-dual computable singleton model. -/
abbrev Portal :=
  {pair : DualNeutralOrEmpty × DualRootedPos //
    pair.1.1 ⋖ pair.2.1}


-- @@ L97-100 verbatim
/-- A fully computable version of the rooted singleton portal code. -/
abbrev PortalCode :=
  Σ p : Portal,
    FinsetFlag (Set.Iic p.1.1.1) × FinsetFlag (Set.Ici p.1.2)


-- @@ L102-104 verbatim
/-- The computable singleton portal-code layer of lower step count `k`. -/
abbrev PortalLayer (k : ℕ) :=
  {c : PortalCode // c.2.1.1.card - 1 = k}


-- @@ L106-109 verbatim
set_option maxRecDepth 100000 in
/-- There are two singleton positive portal flags entering at rank zero. -/
theorem card_portalLayer_zero : Fintype.card (PortalLayer 0) = 2 := by
  decide


-- @@ L111-114 verbatim
set_option maxRecDepth 100000 in
/-- There are two singleton positive portal flags entering at rank one. -/
theorem card_portalLayer_one : Fintype.card (PortalLayer 1) = 2 := by
  decide


-- @@ L116-116 verbatim
end SingletonFace


-- @@ L118-118 verbatim
namespace HansenCombinatorialFace


-- @@ L120-126 verbatim
/-- Portal-vector cardinality expressed without retaining a particular
`Fintype` enumeration of the layer. -/
theorem hansenPortalVector_eq_natCard
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    hansenPortalVector G k = Nat.card (HansenPortalLayer G k) := by
  simp only [hansenPortalVector, Nat.card_eq_fintype_card]


-- @@ L128-138 verbatim
/-- The portal-vector cardinality is independent of the chosen finite
enumeration and decidable equality on the vertex type. -/
theorem hansenPortalVector_eq_of_instances
    {V : Type u} (f₁ f₂ : Fintype V) (d₁ d₂ : DecidableEq V)
    (G : SimpleGraph V) (k : ℕ) :
    @hansenPortalVector V f₁ d₁ G k =
      @hansenPortalVector V f₂ d₂ G k := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rw [@hansenPortalVector_eq_natCard V f₁ d₁ G k,
    @hansenPortalVector_eq_natCard V f₂ d₁ G k]


-- @@ L140-148 verbatim
/-- Restrict an order isomorphism to corresponding lower intervals. -/
private def OrderIso.restrictIic' {P Q : Type*}
    [Preorder P] [Preorder Q] (e : P ≃o Q) (a : P) :
    Set.Iic a ≃o Set.Iic (e a) where
  toFun x := ⟨e x.1, (map_le_map_iff e).mpr x.2⟩
  invFun x := ⟨e.symm x.1, e.symm_apply_le.mpr x.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)
  map_rel_iff' := map_le_map_iff e


-- @@ L150-158 verbatim
/-- Restrict an order isomorphism to corresponding upper intervals. -/
private def OrderIso.restrictIci' {P Q : Type*}
    [Preorder P] [Preorder Q] (e : P ≃o Q) (a : P) :
    Set.Ici a ≃o Set.Ici (e a) where
  toFun x := ⟨e x.1, (map_le_map_iff e).mpr x.2⟩
  invFun x := ⟨e.symm x.1, e.le_symm_apply.mpr x.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)
  map_rel_iff' := map_le_map_iff e


-- @@ L160-166 verbatim
/-- The singleton face order isomorphism restricted to rooted positive
faces. -/
noncomputable def singletonDualRootedPosOrderIso :
    RootedPos (⊥ : SimpleGraph PUnit) ≃o SingletonFace.DualRootedPos where
  toEquiv := singletonFaceOrderIso.toEquiv.subtypeEquiv fun F =>
    (singletonFaceEquiv_isRootedPos F).symm
  map_rel_iff' := map_le_map_iff singletonFaceOrderIso


-- @@ L168-175 verbatim
/-- The singleton face order isomorphism restricted to neutral-or-empty
faces. -/
noncomputable def singletonDualNeutralOrEmptyOrderIso :
    NeutralOrEmpty (⊥ : SimpleGraph PUnit) ≃o
      SingletonFace.DualNeutralOrEmpty where
  toEquiv := singletonFaceOrderIso.toEquiv.subtypeEquiv fun F =>
    (singletonFaceEquiv_isNeutralOrEmpty F).symm
  map_rel_iff' := map_le_map_iff singletonFaceOrderIso


-- @@ L177-185 verbatim
/-- Intrinsic positive singleton portals are the portals in the computable
square face lattice. -/
noncomputable def singletonPortalEquiv :
    HansenPortal (⊥ : SimpleGraph PUnit) ≃ SingletonFace.Portal :=
  (Equiv.prodCongr singletonDualNeutralOrEmptyOrderIso.toEquiv
      singletonDualRootedPosOrderIso.toEquiv).subtypeEquiv fun p => by
    change p.1.1 ⋖ p.2.1 ↔
      singletonFaceOrderIso p.1.1 ⋖ singletonFaceOrderIso p.2.1
    exact (apply_covBy_apply_iff singletonFaceOrderIso).symm


-- @@ L187-195 verbatim
/-- Transport a lower singleton portal interval to a computable finite
flag. -/
private noncomputable def singletonLowerPortalFlagEquiv
    (p : HansenPortal (⊥ : SimpleGraph PUnit)) :
    Flag (Set.Iic p.1.1.1) ≃
      FinsetFlag (Set.Iic (singletonPortalEquiv p).1.1.1) :=
  (Flag.map (OrderIso.restrictIic' singletonFaceOrderIso p.1.1.1)).trans
    (finsetFlagEquiv
      (Set.Iic (singletonPortalEquiv p).1.1.1)).symm


-- @@ L197-205 verbatim
/-- Transport a rooted upper singleton portal interval to a computable
finite flag. -/
private noncomputable def singletonUpperPortalFlagEquiv
    (p : HansenPortal (⊥ : SimpleGraph PUnit)) :
    Flag (Set.Ici p.1.2) ≃
      FinsetFlag (Set.Ici (singletonPortalEquiv p).1.2) :=
  (Flag.map
      (OrderIso.restrictIci' singletonDualRootedPosOrderIso p.1.2)).trans
    (finsetFlagEquiv (Set.Ici (singletonPortalEquiv p).1.2)).symm


-- @@ L207-213 verbatim
/-- The intrinsic singleton portal code is exactly its computable square
model. -/
noncomputable def singletonPortalCodeEquiv :
    HansenPortalCode (⊥ : SimpleGraph PUnit) ≃ SingletonFace.PortalCode :=
  Equiv.sigmaCongr singletonPortalEquiv fun p =>
    Equiv.prodCongr (singletonLowerPortalFlagEquiv p)
      (singletonUpperPortalFlagEquiv p)


-- @@ L215-242 verbatim
/-- The preceding equivalence preserves the lower portal layer. -/
noncomputable def singletonPortalLayerEquiv (k : ℕ) :
    HansenPortalLayer (⊥ : SimpleGraph PUnit) k ≃
      SingletonFace.PortalLayer k :=
  singletonPortalCodeEquiv.subtypeEquiv fun c => by
    let mapped := Flag.map
      (OrderIso.restrictIic' singletonFaceOrderIso c.1.1.1.1) c.2.1
    let finite :=
      (finsetFlagEquiv
        (Set.Iic (singletonPortalEquiv c.1).1.1.1)).symm mapped
    have hrecover :
        finsetFlagEquiv (Set.Iic (singletonPortalEquiv c.1).1.1.1) finite =
          mapped :=
      (finsetFlagEquiv
        (Set.Iic (singletonPortalEquiv c.1).1.1.1)).apply_symm_apply mapped
    have hcard : Nat.card c.2.1 = finite.1.card := by
      calc
        Nat.card c.2.1 = Nat.card mapped :=
          (Flag.card_map
            (OrderIso.restrictIic' singletonFaceOrderIso c.1.1.1.1)
            c.2.1).symm
        _ = finite.1.card := by
          rw [← hrecover]
          exact Flag.card_finsetFlagEquiv finite
    change Nat.card c.2.1 - 1 = k ↔
      ((singletonPortalCodeEquiv c).2.1).1.card - 1 = k
    change Nat.card c.2.1 - 1 = k ↔ finite.1.card - 1 = k
    rw [hcard]


-- @@ L244-249 verbatim
/-- The first singleton portal-vector entry is two. -/
theorem hansenPortalVector_singleton_zero :
    hansenPortalVector (⊥ : SimpleGraph PUnit) 0 = 2 := by
  unfold hansenPortalVector
  rw [Fintype.card_congr (singletonPortalLayerEquiv 0)]
  exact SingletonFace.card_portalLayer_zero


-- @@ L251-256 verbatim
/-- The second singleton portal-vector entry is two. -/
theorem hansenPortalVector_singleton_one :
    hansenPortalVector (⊥ : SimpleGraph PUnit) 1 = 2 := by
  unfold hansenPortalVector
  rw [Fintype.card_congr (singletonPortalLayerEquiv 1)]
  exact SingletonFace.card_portalLayer_one


-- @@ L258-258 verbatim
end HansenCombinatorialFace


-- @@ L260-271 verbatim
/-- The factorially normalized singleton portal polynomial is the constant
two. -/
theorem portalPolynomial_singleton (x : ℝ) :
    portalPolynomial 1
      (fun k =>
        (HansenCombinatorialFace.hansenPortalVector
          (⊥ : SimpleGraph PUnit) k : ℝ)) x = 2 := by
  unfold portalPolynomial
  norm_num [Finset.sum_range_succ,
    HansenCombinatorialFace.hansenPortalVector_singleton_zero,
    HansenCombinatorialFace.hansenPortalVector_singleton_one]
  ring


-- @@ L273-279 verbatim
/-- A graph has constant portal polynomial on the whole real line. -/
def PortalPolynomialConstant {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  IsConstantFunction
    (portalPolynomial (Fintype.card V)
      (fun k =>
        (HansenCombinatorialFace.hansenPortalVector G k : ℝ)))


-- @@ L281-286 verbatim
/-- The singleton Hansen portal polynomial is constant. -/
theorem portalPolynomialConstant_singleton :
    PortalPolynomialConstant (⊥ : SimpleGraph PUnit) := by
  intro x y
  simpa using (portalPolynomial_singleton x).trans
    (portalPolynomial_singleton y).symm


-- @@ L288-326 expanded
/-- Constancy of both factor portal polynomials is preserved by graph join. -/
theorem PortalPolynomialConstant.join {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hAcard : UniformFlagCard (HansenCombinatorialFace A) (Fintype.card V + 3))
    (hBcard : UniformFlagCard (HansenCombinatorialFace B) (Fintype.card W + 3))
    (hA : PortalPolynomialConstant A) (hB : PortalPolynomialConstant B) :
    PortalPolynomialConstant (graphJoin A B) :=
  by
  intro x y
  let a : ℕ → ℝ := fun k => (HansenCombinatorialFace.hansenPortalVector A k : ℝ)
  let b : ℕ → ℝ := fun k => (HansenCombinatorialFace.hansenPortalVector B k : ℝ)
  have hpoly (z : ℝ) :
    portalPolynomial (Fintype.card (V ⊕ W))
        (fun k => (HansenCombinatorialFace.hansenPortalVector (graphJoin A B) k : ℝ)) z =
      portalPolynomial (Fintype.card V) a z * portalPolynomial (Fintype.card W) b z :=
    by
    rw [Fintype.card_sum]
    calc
      portalPolynomial (Fintype.card V + Fintype.card W)
            (fun k => (HansenCombinatorialFace.hansenPortalVector (graphJoin A B) k : ℝ)) z =
          portalPolynomial (Fintype.card V + Fintype.card W)
            (portalShuffleConvolution (Fintype.card V) (Fintype.card W) a b) z :=
        by
        congr 1
        funext k
        exact
          HansenCombinatorialFace.hansenPortalVector_join_cast_eq_portalShuffleConvolution A B
            hAcard hBcard k
      _ = portalPolynomial (Fintype.card V) a z * portalPolynomial (Fintype.card W) b z :=
        portalPolynomial_convolution (Fintype.card V) (Fintype.card W) a b z
  rw [hpoly x, hpoly y, hA x y, hB x y]


-- @@ L328-359 verbatim
/-- Correlation is an equality if at least one portal polynomial is
constant. -/
theorem portalShuffleConvolution_mass_normalized_eq_of_constant
    {n m : ℕ} {a b : ℕ → ℝ}
    (hconstant : IsConstantFunction (portalPolynomial n a) ∨
      IsConstantFunction (portalPolynomial m b)) :
    ( ∑ k ∈ Finset.range (n + 1), a k) /
          ((n + 1).factorial : ℝ) *
        ((∑ l ∈ Finset.range (m + 1), b l) /
          ((m + 1).factorial : ℝ)) =
      (∑ s ∈ Finset.range (n + m + 1),
          portalShuffleConvolution n m a b s) /
        ((n + m + 1).factorial : ℝ) := by
  rw [← integral_portalPolynomial n a,
    ← integral_portalPolynomial m b,
    ← integral_portalPolynomial (n + m)
      (portalShuffleConvolution n m a b)]
  rw [intervalIntegral.integral_congr (fun x _ =>
    portalPolynomial_convolution n m a b x)]
  rcases hconstant with ha | hb
  · let c := portalPolynomial n a 0
    have hc : portalPolynomial n a = fun _ => c := by
      funext x
      exact ha x 0
    rw [hc, intervalIntegral.integral_const_mul]
    simp [c]
  · let c := portalPolynomial m b 0
    have hc : portalPolynomial m b = fun _ => c := by
      funext x
      exact hb x 0
    rw [hc, intervalIntegral.integral_mul_const]
    simp [c]


-- @@ L361-435 expanded
/-- The normalized Hansen full-flag join inequality is exact when one
factor portal polynomial is constant. -/
theorem hansenFullFlagRatio_join_eq_of_portalPolynomialConstant {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : UniformFlagCard (HansenCombinatorialFace A) (Fintype.card V + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (Fintype.card W + 3))
    (hconstant : PortalPolynomialConstant A ∨ PortalPolynomialConstant B) :
    hansenFullFlagRatio A * hansenFullFlagRatio B = hansenFullFlagRatio (graphJoin A B) := by
  classical
  let n := Fintype.card V
  let m := Fintype.card W
  let a : ℕ → ℝ := fun k => (HansenCombinatorialFace.hansenPortalVector A k : ℝ)
  let b : ℕ → ℝ := fun k => (HansenCombinatorialFace.hansenPortalVector B k : ℝ)
  have hconstant' :
    IsConstantFunction (portalPolynomial n a) ∨ IsConstantFunction (portalPolynomial m b) := by
    simpa only [PortalPolynomialConstant, n, m, a, b] using hconstant
  have hmass :=
    portalShuffleConvolution_mass_normalized_eq_of_constant (n := n) (m := m) (a := a) (b := b)
      hconstant'
  have hjoinUniform :
    UniformFlagCard (HansenCombinatorialFace (graphJoin A B)) (Fintype.card (V ⊕ W) + 3) :=
    by
    have h := UniformFlagCard.hansenJoin A B hA hB
    have hlen : (Fintype.card V + 3) + (Fintype.card W + 3) - 3 = Fintype.card (V ⊕ W) + 3 :=
      by
      simp only [Fintype.card_sum]
      omega
    rw [hlen] at h
    exact h
  have hconv (s : ℕ) :
    (HansenCombinatorialFace.hansenPortalVector (graphJoin A B) s : ℝ) =
      portalShuffleConvolution n m a b s :=
    by
    exact
      HansenCombinatorialFace.hansenPortalVector_join_cast_eq_portalShuffleConvolution A B hA hB s
  rw [hansenFullFlagRatio_eq_portalVector_mass A hA, hansenFullFlagRatio_eq_portalVector_mass B hB,
    hansenFullFlagRatio_eq_portalVector_mass (graphJoin A B) hjoinUniform]
  simp only [Fintype.card_sum]
  simp_rw [hconv]
  change
    ((∑ k ∈ Finset.range (n + 1), a k) / (2 ^ n * ((n + 1).factorial : ℝ))) *
        ((∑ l ∈ Finset.range (m + 1), b l) / (2 ^ m * ((m + 1).factorial : ℝ))) =
      (∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
        (2 ^ (n + m) * ((n + m + 1).factorial : ℝ))
  calc
    ((∑ k ∈ Finset.range (n + 1), a k) / (2 ^ n * ((n + 1).factorial : ℝ))) *
          ((∑ l ∈ Finset.range (m + 1), b l) / (2 ^ m * ((m + 1).factorial : ℝ))) =
        (((∑ k ∈ Finset.range (n + 1), a k) / ((n + 1).factorial : ℝ)) *
            ((∑ l ∈ Finset.range (m + 1), b l) / ((m + 1).factorial : ℝ))) /
          2 ^ (n + m) :=
      by
      rw [pow_add]
      ring
    _ =
        ((∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
            ((n + m + 1).factorial : ℝ)) /
          2 ^ (n + m) :=
      by rw [hmass]
    _ =
        (∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
          (2 ^ (n + m) * ((n + m + 1).factorial : ℝ)) :=
      by ring


-- @@ L437-437 verbatim
namespace Cotree


-- @@ L439-448 verbatim
private theorem compl_eq_top_iff_eq_bot_local
    {X : Type*} (G : SimpleGraph X) :
    Gᶜ = ⊤ ↔ G = ⊥ := by
  constructor
  · intro h
    have hc := congrArg (fun H : SimpleGraph X => Hᶜ) h
    simpa using hc
  · intro h
    rw [h]
    simp


-- @@ L450-459 verbatim
private theorem compl_eq_bot_iff_eq_top_local
    {X : Type*} (G : SimpleGraph X) :
    Gᶜ = ⊥ ↔ G = ⊤ := by
  constructor
  · intro h
    have hc := congrArg (fun H : SimpleGraph X => Hᶜ) h
    simpa using hc
  · intro h
    rw [h]
    simp


-- @@ L461-555 verbatim
/-- Completeness and edgelessness are carried together: a complete
evaluation has constant primal portal polynomial, while an edgeless
evaluation has constant portal polynomial after complementation. -/
theorem portalPolynomialConstant_extremal :
    ∀ T : Cotree,
      (T.eval = ⊤ → PortalPolynomialConstant T.eval) ∧
      (T.eval = ⊥ → PortalPolynomialConstant T.evalᶜ) := by
  intro T
  induction T with
  | leaf =>
      have hcard : Fintype.card (Vert .leaf) = 1 := by
        have f : Vert .leaf ≃ PUnit := Equiv.refl PUnit
        simpa using Fintype.card_congr f
      have hw0 :
          HansenCombinatorialFace.hansenPortalVector (eval .leaf) 0 = 2 := by
        change
          @HansenCombinatorialFace.hansenPortalVector PUnit
              (instFintypeVert .leaf) (instDecidableEqVert .leaf)
              (⊥ : SimpleGraph PUnit) 0 = 2
        calc
          _ = HansenCombinatorialFace.hansenPortalVector
                (⊥ : SimpleGraph PUnit) 0 :=
            HansenCombinatorialFace.hansenPortalVector_eq_of_instances
              (instFintypeVert .leaf) inferInstance
              (instDecidableEqVert .leaf) inferInstance _ _
          _ = 2 :=
            HansenCombinatorialFace.hansenPortalVector_singleton_zero
      have hw1 :
          HansenCombinatorialFace.hansenPortalVector (eval .leaf) 1 = 2 := by
        change
          @HansenCombinatorialFace.hansenPortalVector PUnit
              (instFintypeVert .leaf) (instDecidableEqVert .leaf)
              (⊥ : SimpleGraph PUnit) 1 = 2
        calc
          _ = HansenCombinatorialFace.hansenPortalVector
                (⊥ : SimpleGraph PUnit) 1 :=
            HansenCombinatorialFace.hansenPortalVector_eq_of_instances
              (instFintypeVert .leaf) inferInstance
              (instDecidableEqVert .leaf) inferInstance _ _
          _ = 2 :=
            HansenCombinatorialFace.hansenPortalVector_singleton_one
      have hleaf : PortalPolynomialConstant (eval .leaf) := by
        intro x y
        rw [hcard]
        unfold portalPolynomial
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        rw [hw0, hw1]
        norm_num
        ring
      constructor
      · intro _
        exact hleaf
      · intro _
        have htop : (⊤ : SimpleGraph (Vert .leaf)) = ⊥ := by
          change (⊤ : SimpleGraph PUnit) = ⊥
          ext u v
          have huv : u = v := Subsingleton.elim _ _
          subst v
          simp
        have hself : (eval .leaf)ᶜ = eval .leaf := by
          simp [eval, htop]
        rw [hself]
        exact hleaf
  | compl A ih =>
      constructor
      · intro htop
        change @PortalPolynomialConstant (Vert A) (instFintypeVert A)
          (instDecidableEqVert A) (eval A)ᶜ
        change A.evalᶜ = ⊤ at htop
        have hbot : A.eval = ⊥ :=
          (compl_eq_top_iff_eq_bot_local A.eval).mp htop
        exact ih.2 hbot
      · intro hbot
        change @PortalPolynomialConstant (Vert A) (instFintypeVert A)
          (instDecidableEqVert A) ((eval A)ᶜ)ᶜ
        change A.evalᶜ = ⊥ at hbot
        have htop : A.eval = ⊤ :=
          (compl_eq_bot_iff_eq_top_local A.eval).mp hbot
        rw [compl_compl]
        exact ih.1 htop
  | sum A B ihA ihB =>
      constructor
      · intro htop
        exact False.elim (eval_sum_ne_top A B htop)
      · intro hbot
        have hAB := (eval_sum_eq_bot_iff A B).mp hbot
        have hAc : PortalPolynomialConstant A.evalᶜ := ihA.2 hAB.1
        have hBc : PortalPolynomialConstant B.evalᶜ := ihB.2 hAB.2
        have hjoin := PortalPolynomialConstant.join A.evalᶜ B.evalᶜ
          (UniformFlagCard.hansenCompl A.eval (uniformFlagCard_eval A))
          (UniformFlagCard.hansenCompl B.eval (uniformFlagCard_eval B))
          hAc hBc
        change PortalPolynomialConstant ((A.eval ⊕g B.eval)ᶜ)
        rw [compl_sum_eq_join]
        exact hjoin


-- @@ L557-561 verbatim
/-- The portal polynomial of a complete cotree evaluation is constant. -/
theorem portalPolynomialConstant_of_eval_eq_top
    (T : Cotree) (hT : T.eval = ⊤) :
    PortalPolynomialConstant T.eval :=
  (portalPolynomialConstant_extremal T).1 hT


-- @@ L563-568 verbatim
/-- If a cotree evaluation is edgeless, the portal polynomial of its
complement is constant. -/
theorem portalPolynomialConstant_compl_of_eval_eq_bot
    (T : Cotree) (hT : T.eval = ⊥) :
    PortalPolynomialConstant T.evalᶜ :=
  (portalPolynomialConstant_extremal T).2 hT


-- @@ L570-592 expanded
/-- A cotree union is an exact normalized full-flag product when at least
one child is edgeless. -/
theorem hansenFullFlagRatio_sum_eq_of_eval_eq_bot (A B : Cotree) (hbot : A.eval = ⊥ ∨ B.eval = ⊥) :
    hansenFullFlagRatio A.eval * hansenFullFlagRatio B.eval =
      hansenFullFlagRatio (A.eval ⊕g B.eval) :=
  by
  have hconstant : PortalPolynomialConstant A.evalᶜ ∨ PortalPolynomialConstant B.evalᶜ :=
    by
    rcases hbot with hA | hB
    · exact Or.inl (portalPolynomialConstant_compl_of_eval_eq_bot A hA)
    · exact Or.inr (portalPolynomialConstant_compl_of_eval_eq_bot B hB)
  have hjoin :=
    hansenFullFlagRatio_join_eq_of_portalPolynomialConstant A.evalᶜ B.evalᶜ
      (UniformFlagCard.hansenCompl A.eval (uniformFlagCard_eval A))
      (UniformFlagCard.hansenCompl B.eval (uniformFlagCard_eval B)) hconstant
  calc
    hansenFullFlagRatio A.eval * hansenFullFlagRatio B.eval =
        hansenFullFlagRatio A.evalᶜ * hansenFullFlagRatio B.evalᶜ :=
      by simp
    _ = hansenFullFlagRatio (graphJoin A.evalᶜ B.evalᶜ) := hjoin
    _ = hansenFullFlagRatio (A.eval ⊕g B.eval) := by
      rw [← compl_sum_eq_join, hansenFullFlagRatio_compl]


-- @@ L594-631 verbatim
/-- Every threshold cotree attains equality in the normalized Hansen
full-flag bound. -/
theorem hansenFullFlagRatio_eq_one_of_isThreshold :
    ∀ T : Cotree, T.IsThreshold → hansenFullFlagRatio T.eval = 1 := by
  intro T
  induction T with
  | leaf =>
      intro _
      let e : (⊥ : SimpleGraph PUnit) ≃g eval .leaf := SimpleGraph.Iso.refl
      have hcount : hansenFullFlagCount (eval .leaf) = 8 := by
        rw [← hansenFullFlagCount_iso e]
        exact hansenFullFlagCount_singleton
      have hcard : Fintype.card (Vert .leaf) = 1 := by
        have f : Vert .leaf ≃ PUnit := Equiv.refl PUnit
        simpa using Fintype.card_congr f
      unfold hansenFullFlagRatio
      rw [hcount, hcard]
      norm_num
  | compl A ih =>
      intro hA
      change @hansenFullFlagRatio (Vert A) (instFintypeVert A)
        (instDecidableEqVert A) (eval A)ᶜ = 1
      rw [hansenFullFlagRatio_compl]
      exact ih hA
  | sum A B ihA ihB =>
      rintro ⟨hA, hB, hbot⟩
      let _ : Fintype (Vert A ⊕ Vert B) := instFintypeVert (.sum A B)
      let _ : DecidableEq (Vert A ⊕ Vert B) :=
        instDecidableEqVert (.sum A B)
      change hansenFullFlagRatio (A.eval ⊕g B.eval) = 1
      have hsum :
          hansenFullFlagRatio A.eval * hansenFullFlagRatio B.eval =
            hansenFullFlagRatio (A.eval ⊕g B.eval) :=
        hansenFullFlagRatio_sum_eq_of_eval_eq_bot A B hbot
      calc
        hansenFullFlagRatio (A.eval ⊕g B.eval) =
            hansenFullFlagRatio A.eval * hansenFullFlagRatio B.eval := hsum.symm
        _ = 1 := by rw [ihA hA, ihB hB, one_mul]


-- @@ L633-633 verbatim
end Cotree


-- @@ L635-635 verbatim
end HansenCograph
