/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.BinderNotation
public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Calculus
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental


-- @@ L12-12 verbatim
/-! # Basic -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace FirstOrder


-- @@ L20-20 verbatim
namespace Theory

-- @@ L21-21 verbatim
namespace Alt


-- @@ L23-23 verbatim
variable {L : Language} {T U : Theory L}


-- @@ L25-25 expanded
instance [s : WeakerThan T U] : WeakerThan T U.alt.thy :=
  s


-- @@ L27-27 expanded
instance [s : WeakerThan T U] : WeakerThan T.alt U.alt :=
  ⟨fun _ b ↦ s.pbl b⟩


-- @@ L29-29 verbatim
end Alt

-- @@ L30-30 verbatim
end Theory



-- @@ L33-33 verbatim
namespace DerivabilityCondition


-- @@ L35-35 verbatim
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]


-- @@ L37-41 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure ProvabilityPredicate (T₀ : Theory L) (T : Theory L) where
  /-- Imported declaration from the Incompleteness formalization. -/
  prov : Semisentence L 1
  spec {σ : Sentence L} :
    Provable₀ T σ → Provable₀ T₀ (LO.FirstOrder.Rewriting.substitute prov ![GoedelQuote.quote σ])


-- @@ L43-43 verbatim
namespace ProvabilityPredicate


-- @@ L45-45 verbatim
variable {T₀ T : Theory L}


-- @@ L47-48 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[coe]
def pr (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L :=
  LO.FirstOrder.Rewriting.substitute 𝔅.prov ![GoedelQuote.quote σ]


-- @@ L50-50 verbatim
instance : CoeFun (ProvabilityPredicate T₀ T) (fun _ => Sentence L → Sentence L) := ⟨pr⟩


-- @@ L52-53 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def con (𝔅 : ProvabilityPredicate T₀ T) : Sentence L :=
  Tilde.tilde (𝔅 ⊥)


-- @@ L55-55 verbatim
end ProvabilityPredicate


-- @@ L57-61 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Diagonalization (T : Theory L) where
  /-- Imported declaration from the Incompleteness formalization. -/
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) :
    Provable₀ T
      (LogicalConnective.iff (fixpoint θ)
        (LO.FirstOrder.Rewriting.substitute θ ![GoedelQuote.quote (fixpoint θ)]))


-- @@ L63-63 verbatim
namespace ProvabilityPredicate


-- @@ L65-65 verbatim
variable {T₀ T : Theory L}


-- @@ L67-69 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HBL2 (𝔅 : ProvabilityPredicate T₀ T) where
  D2 {σ τ : Sentence L} : Provable₀ T₀ (Arrow.arrow (𝔅 (Arrow.arrow σ τ)) (Arrow.arrow (𝔅 σ) (𝔅 τ)))


-- @@ L71-73 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HBL3 (𝔅 : ProvabilityPredicate T₀ T) where
  D3 {σ : Sentence L} : Provable₀ T₀ (Arrow.arrow (𝔅 σ) (𝔅 (𝔅 σ)))


-- @@ L75-76 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HBL (𝔅 : ProvabilityPredicate T₀ T) extends 𝔅.HBL2, 𝔅.HBL3


-- @@ L78-80 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Loeb (𝔅 : ProvabilityPredicate T₀ T) where
  LT {σ : Sentence L} : Provable₀ T (Arrow.arrow (𝔅 σ) σ) → Provable₀ T σ


-- @@ L82-84 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class FormalizedLoeb (𝔅 : ProvabilityPredicate T₀ T) where
  FLT {σ : Sentence L} : Provable₀ T₀ (Arrow.arrow (𝔅 (Arrow.arrow (𝔅 σ) σ)) (𝔅 σ))


-- @@ L86-88 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Rosser (𝔅 : ProvabilityPredicate T₀ T) where
  Ro {σ : Sentence L} : Provable₀ T (Tilde.tilde σ) → Provable₀ T₀ (Tilde.tilde (𝔅 σ))


-- @@ L90-90 verbatim
section «lp_section_1»


-- @@ L92-92 verbatim
open LO.Entailment


-- @@ L94-97 expanded
variable [L.DecidableEq] {T₀ T : Theory L} [WeakerThan T₀ T] {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL]
  {σ τ : Sentence L}


-- @@ L99-101 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D1 : Provable₀ T σ → Provable₀ T₀ (𝔅 σ) :=
  𝔅.spec


-- @@ L102-102 verbatim
alias D2 := HBL2.D2

-- @@ L103-103 verbatim
alias D3 := HBL3.D3

-- @@ L104-104 verbatim
alias LT := Loeb.LT

-- @@ L105-105 verbatim
alias FLT := FormalizedLoeb.FLT

-- @@ L106-106 verbatim
alias Ro := Rosser.Ro


-- @@ L108-113 expanded
omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D1_shift : Provable₀ T σ → Provable₀ T (𝔅 σ) := by intro h;
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt); apply D1 h;


-- @@ L115-119 expanded
omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D2_shift [𝔅.HBL2] :
    Provable₀ T (Arrow.arrow (𝔅 (Arrow.arrow σ τ)) (Arrow.arrow (𝔅 σ) (𝔅 τ))) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt); apply D2;


-- @@ L121-125 expanded
omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D3_shift [𝔅.HBL3] : Provable₀ T (Arrow.arrow (𝔅 σ) (𝔅 (𝔅 σ))) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt); apply D3;


-- @@ L127-131 expanded
omit [L.DecidableEq] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma FLT_shift [𝔅.FormalizedLoeb] : Provable₀ T (Arrow.arrow (𝔅 (Arrow.arrow (𝔅 σ) σ)) (𝔅 σ)) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt); apply 𝔅.FLT;


-- @@ L133-137 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] [𝔅.HBL] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma D2' [𝔅.HBL2] : Provable₀ T₀ (𝔅 (Arrow.arrow σ τ)) → Provable₀ T₀ (Arrow.arrow (𝔅 σ) (𝔅 τ)) :=
  by intro h; exact mdp D2 h;


-- @@ L139-141 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_imply (h : Provable₀ T (Arrow.arrow σ τ)) :
    Provable₀ T₀ (Arrow.arrow (𝔅 σ) (𝔅 τ)) :=
  D2' <| D1 h


-- @@ L143-148 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_iff (h : Provable₀ T (LogicalConnective.iff σ τ)) :
    Provable₀ T₀ (LogicalConnective.iff (𝔅 σ) (𝔅 τ)) :=
  by
  apply iff_intro!; · exact prov_distribute_imply <| and₁'! h;
  · exact prov_distribute_imply <| and₂'! h;


-- @@ L150-155 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_and :
    Provable₀ T₀ (Arrow.arrow (𝔅 (Wedge.wedge σ τ)) (Wedge.wedge (𝔅 σ) (𝔅 τ))) := by
  have h₁ : Provable₀ T₀ (Arrow.arrow (𝔅 (Wedge.wedge σ τ)) (𝔅 σ)) := D2' <| D1 and₁!;
  have h₂ : Provable₀ T₀ (Arrow.arrow (𝔅 (Wedge.wedge σ τ)) (𝔅 τ)) := D2' <| D1 and₂!;
  exact imply_right_and! h₁ h₂;


-- @@ L157-161 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_distribute_and' :
    Provable₀ T₀ (𝔅 (Wedge.wedge σ τ)) → Provable₀ T₀ (Wedge.wedge (𝔅 σ) (𝔅 τ)) := fun h =>
  mdp prov_distribute_and h


-- @@ L163-169 expanded
omit [L.DecidableEq] [WeakerThan T₀ T] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma prov_collect_and :
    Provable₀ T₀ (Arrow.arrow (Wedge.wedge (𝔅 σ) (𝔅 τ)) (𝔅 (Wedge.wedge σ τ))) := by
  have h₁ : Provable₀ T₀ (Arrow.arrow (𝔅 σ) (𝔅 (Arrow.arrow τ (Wedge.wedge σ τ)))) :=
    prov_distribute_imply <| and₃!;
  have h₂ :
    Provable₀ T₀
      (Arrow.arrow (𝔅 (Arrow.arrow τ (Wedge.wedge σ τ)))
        (Arrow.arrow (𝔅 τ) (𝔅 (Wedge.wedge σ τ)))) :=
    D2;
  apply and_imply_iff_imply_imply'!.mpr; exact imp_trans''! h₁ h₂;


-- @@ L171-171 verbatim
end «lp_section_1»


-- @@ L173-173 verbatim
end ProvabilityPredicate


-- @@ L175-175 verbatim
variable {T₀ T : Theory L} {𝔅 : ProvabilityPredicate T₀ T}


-- @@ L177-177 verbatim
open LO.Entailment

-- @@ L178-178 verbatim
open Diagonalization

-- @@ L179-179 verbatim
open ProvabilityPredicate


-- @@ L181-185 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.goedel [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) : Sentence L :=
  fixpoint T₀ (Tilde.tilde (LO.FirstOrder.Rewriting.substitute 𝔅.prov (vecCons #0 ![])))


-- @@ L187-187 verbatim
section «lp_section_2»


-- @@ L189-189 verbatim
variable [Diagonalization T₀]


-- @@ L191-191 verbatim
local notation "γ" => 𝔅.goedel


-- @@ L193-201 expanded
lemma goedel_spec : Provable₀ T₀ (LogicalConnective.iff γ (Tilde.tilde (𝔅 γ))) :=
  by
  convert
    (diag (T := T₀) (Tilde.tilde (LO.FirstOrder.Rewriting.substitute 𝔅.prov (vecCons #0 ![]))));
  case e'_4 => unfold goedel pr;
    change
      Tilde.tilde (app (Rew.substs ![_]) 𝔅.prov) =
        app (Rew.substs ![_]) (Tilde.tilde (app (Rew.substs ![#0]) 𝔅.prov));
    rw [LogicalConnective.HomClass.map_neg (Rewriting.app (Rew.substs ![_]))];
    rw [← TransitiveRewriting.comp_app, Rew.substs_comp_substs]; simp_all
  case e'_3 => unfold goedel; rfl;


-- @@ L203-203 expanded
variable [WeakerThan T₀ T]


-- @@ L205-205 expanded
private lemma goedel_specAux₁ : Provable₀ T (LogicalConnective.iff γ (Tilde.tilde (𝔅 γ))) :=
  WeakerThan.pbl (𝓢 := T₀.alt) goedel_spec


-- @@ L207-209 expanded
private lemma goedel_specAux₂ : Provable₀ T (Arrow.arrow (Tilde.tilde γ) (𝔅 γ)) :=
  contra₂'! <| and₂'! goedel_specAux₁


-- @@ L211-211 verbatim
end «lp_section_2»


-- @@ L213-216 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.GoedelSound
    (𝔅 : ProvabilityPredicate T₀ T) [Diagonalization T₀] where
  γ_sound : Provable₀ T (𝔅 𝔅.goedel) → Provable₀ T 𝔅.goedel


-- @@ L218-218 verbatim
open GoedelSound


-- @@ L220-220 verbatim
section «lp_section_3»


-- @@ L222-222 expanded
variable [L.DecidableEq] [WeakerThan T₀ T] [Diagonalization T₀]


-- @@ L224-224 verbatim
local notation "γ" => 𝔅.goedel


-- @@ L226-226 verbatim
variable [Entailment.Consistent T]


-- @@ L228-236 expanded
omit [L.DecidableEq] in
theorem unprovable_goedel : Unprovable₀ T γ :=
  by
  intro h; have h₁ : Provable₀ T (𝔅 γ) := Entailment.WeakerThan.pbl (𝓢 := T₀.alt) (𝔅.spec h);
  have h₂ : Provable₀ T (Tilde.tilde (𝔅 γ)) := mdp (and₁'! goedel_specAux₁) h;
  have : Provable₀ T ⊥ := mdp (negEquiv'!.mp h₂) h₁;
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <|
      inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction;


-- @@ L238-247 expanded
omit [L.DecidableEq] in
theorem unrefutable_goedel [𝔅.GoedelSound] : Unprovable₀ T (Tilde.tilde γ) := by
  classical intro h₂; have h₁ : Provable₀ T γ := γ_sound <| mdp goedel_specAux₂ h₂;
  have : Provable₀ T ⊥ := mdp (negEquiv'!.mp h₂) h₁;
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <|
      inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this);
  contradiction;


-- @@ L249-255 expanded
omit [L.DecidableEq] in
theorem goedel_independent [𝔅.GoedelSound] : Entailment.Undecidable T ↑γ := by
  classical
  suffices Unprovable₀ T γ ∧ Unprovable₀ T (Tilde.tilde γ) by
    simpa [Entailment.Undecidable, not_or, unprovable₀_iff] using this
  constructor
  · apply unprovable_goedel
  · apply unrefutable_goedel


-- @@ L257-260 verbatim
omit [L.DecidableEq] in
theorem first_incompleteness [𝔅.GoedelSound]
  : ¬Entailment.Complete T :=
    Entailment.incomplete_iff_exists_undecidable.mpr ⟨γ, goedel_independent⟩


-- @@ L262-262 verbatim
end «lp_section_3»


-- @@ L264-264 verbatim
section «lp_section_4»


-- @@ L266-266 verbatim
variable [𝔅.HBL]


-- @@ L268-268 verbatim
section


-- @@ L270-270 verbatim
variable [L.DecidableEq]


-- @@ L272-272 verbatim
local notation "γ" => 𝔅.goedel


-- @@ L274-276 expanded
lemma formalized_consistent_of_existance_unprovable :
    Provable₀ T₀ (Arrow.arrow (Tilde.tilde (𝔅 σ)) 𝔅.con) :=
  contra₀'! <| mdp 𝔅.D2 (D1 efq!)


-- @@ L278-289 expanded
omit [L.DecidableEq] in
private lemma consistency_lemma_2 :
    Provable₀ T₀ (Arrow.arrow (Arrow.arrow (𝔅 σ) (𝔅 (Tilde.tilde σ))) (Arrow.arrow (𝔅 σ) (𝔅 ⊥))) :=
  by
  have : Provable₀ T (Arrow.arrow σ (Arrow.arrow (Tilde.tilde σ) ⊥)) :=
    and_imply_iff_imply_imply'!.mp lac!
  have : Provable₀ T₀ (Arrow.arrow (𝔅 σ) (𝔅 (Arrow.arrow (Tilde.tilde σ) ⊥))) :=
    prov_distribute_imply this;
  have : Provable₀ T₀ (Arrow.arrow (𝔅 σ) (Arrow.arrow (𝔅 (Tilde.tilde σ)) (𝔅 ⊥))) :=
    imp_trans''! this D2;
  -- TODO: more simple proof
  apply FiniteContext.deduct'!; apply FiniteContext.deduct!;
  have d₁ : Provable T₀.alt [(𝔅 σ), Arrow.arrow (𝔅 σ) (𝔅 (Tilde.tilde σ))] (𝔅 σ) :=
    FiniteContext.by_axm!;
  have d₂ :
    Provable T₀.alt [(𝔅 σ), Arrow.arrow (𝔅 σ) (𝔅 (Tilde.tilde σ))]
      (Arrow.arrow (𝔅 σ) (𝔅 (Tilde.tilde σ))) :=
    FiniteContext.by_axm!;
  have d₃ : Provable T₀.alt [(𝔅 σ), Arrow.arrow (𝔅 σ) (𝔅 (Tilde.tilde σ))] (𝔅 (Tilde.tilde σ)) :=
    mdp d₂ d₁;
  exact mdp (mdp (FiniteContext.of'! this) d₁) d₃;


-- @@ L291-291 verbatim
end


-- @@ L293-293 verbatim
variable [Diagonalization T₀]


-- @@ L295-295 verbatim
local notation "γ" => 𝔅.goedel


-- @@ L297-304 expanded
/-- Formalized First Incompleteness Theorem -/
theorem _root_.LO.FirstOrder.DerivabilityCondition.formalized_unprovable_goedel [WeakerThan T₀ T] :
    Provable₀ T (Arrow.arrow 𝔅.con (Tilde.tilde (𝔅 γ))) := by
  have h₁ : Provable₀ T₀ (Arrow.arrow (𝔅 γ) (𝔅 (𝔅 γ))) := D3;
  have h₂ : Provable₀ T (Arrow.arrow (𝔅 γ) (Tilde.tilde γ)) :=
    WeakerThan.pbl <| contra₁'! <| and₁'! goedel_spec;
  have h₃ : Provable₀ T₀ (Arrow.arrow (𝔅 (𝔅 γ)) (𝔅 (Tilde.tilde γ))) := prov_distribute_imply h₂;
  exact WeakerThan.pbl <| contra₀'! <| mdp consistency_lemma_2 (imp_trans''! h₁ h₃);


-- @@ L306-309 expanded
theorem _root_.LO.FirstOrder.DerivabilityCondition.iff_goedel_consistency [L.DecidableEq]
    [WeakerThan T₀ T] : Provable₀ T (LogicalConnective.iff γ 𝔅.con) :=
  iff_trans''! goedel_specAux₁ <|
    iff_intro! (WeakerThan.pbl (𝓢 := T₀.alt) formalized_consistent_of_existance_unprovable)
      formalized_unprovable_goedel


-- @@ L311-314 expanded
theorem _root_.LO.FirstOrder.DerivabilityCondition.unprovable_consistency [L.DecidableEq]
    [WeakerThan T₀ T] [Entailment.Consistent T] : Unprovable₀ T 𝔅.con :=
  unprovable_iff! iff_goedel_consistency |>.mp <| unprovable_goedel


-- @@ L316-319 expanded
theorem _root_.LO.FirstOrder.DerivabilityCondition.unrefutable_consistency [L.DecidableEq]
    [WeakerThan T₀ T] [Entailment.Consistent T] [𝔅.GoedelSound] :
    Unprovable₀ T (Tilde.tilde 𝔅.con) :=
  unprovable_iff! (neg_replace_iff'! <| iff_goedel_consistency) |>.mp <| unrefutable_goedel


-- @@ L321-321 verbatim
end «lp_section_4»



-- @@ L324-324 verbatim
section «lp_section_5»


-- @@ L326-329 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.kreisel [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L :=
  fixpoint T₀
    (Arrow.arrow (LO.FirstOrder.Rewriting.substitute 𝔅.prov (vecCons #0 ![]))
      (LO.FirstOrder.Rewriting.substitute σ ![]))


-- @@ L331-331 verbatim
section «lp_section_6»


-- @@ L333-333 verbatim
variable {𝔅 : ProvabilityPredicate T₀ T} [L.DecidableEq] [𝔅.HBL] [Diagonalization T₀]


-- @@ L335-335 verbatim
local notation "κ(" σ ")" => 𝔅.kreisel σ


-- @@ L337-351 expanded
omit [L.DecidableEq] [𝔅.HBL] in
lemma _root_.LO.FirstOrder.DerivabilityCondition.kreisel_spec (σ : Sentence L) :
    Provable₀ T₀ (LogicalConnective.iff κ(σ) (Arrow.arrow (𝔅 (κ(σ))) σ)) :=
  by
  convert
    (diag (T := T₀)
      (Arrow.arrow (LO.FirstOrder.Rewriting.substitute 𝔅.prov (vecCons #0 ![]))
        (LO.FirstOrder.Rewriting.substitute σ ![])));
  case e'_4 =>
    unfold kreisel pr;
    change
      Arrow.arrow (app (Rew.substs ![_]) 𝔅.prov) σ =
        app (Rew.substs ![_])
          (Arrow.arrow (app (Rew.substs ![#0]) 𝔅.prov) (app (Rew.substs ![]) σ));
    rw [LogicalConnective.HomClass.map_imply (Rewriting.app (Rew.substs ![_]))];
    rw [← TransitiveRewriting.comp_app, Rew.substs_comp_substs]; congr 1; · simp_all
    · rw [← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
      simp only [Matrix.empty_eq, Rew.substs_zero, ReflectiveRewriting.id_app];
  case e'_3 => unfold kreisel; rfl;


-- @@ L353-356 expanded
omit [L.DecidableEq] in
private lemma kreisel_specAux₁ [WeakerThan T₀ T] (σ : Sentence L) :
    Provable₀ T₀ (Arrow.arrow (𝔅 κ(σ)) (𝔅 σ)) :=
  mdp₁ (imp_trans''! (mdp D2 (D1 (WeakerThan.pbl <| and₁'! (kreisel_spec σ)))) D2) D3


-- @@ L358-361 expanded
omit [L.DecidableEq] [𝔅.HBL] in
private lemma kreisel_specAux₂ (σ : Sentence L) :
    Provable₀ T₀ (Arrow.arrow (Arrow.arrow (𝔅 κ(σ)) σ) κ(σ)) :=
  and₂'! (kreisel_spec σ)


-- @@ L363-363 verbatim
end «lp_section_6»


-- @@ L365-365 verbatim
section «lp_section_7»


-- @@ L367-367 expanded
variable [L.DecidableEq] [WeakerThan T₀ T] [Diagonalization T₀] [𝔅.HBL]


-- @@ L369-369 verbatim
local notation "κ(" σ ")" => 𝔅.kreisel σ


-- @@ L371-377 expanded
omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.loeb_theorm
    (H : Provable₀ T (Arrow.arrow (𝔅 σ) σ)) : Provable₀ T σ := by
  have d₁ : Provable₀ T (Arrow.arrow (𝔅 (𝔅.kreisel σ)) σ) :=
    imp_trans''! (WeakerThan.pbl (kreisel_specAux₁ σ)) H;
  have d₂ : Provable₀ T (𝔅 (𝔅.kreisel σ)) :=
    WeakerThan.pbl (𝓢 := T₀.alt) (D1 <| mdp (WeakerThan.pbl (kreisel_specAux₂ σ)) d₁);
  exact mdp d₁ d₂;


-- @@ L379-379 verbatim
instance : 𝔅.Loeb := ⟨loeb_theorm (T := T)⟩


-- @@ L381-388 expanded
omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.formalized_loeb_theorem :
    Provable₀ T₀ (Arrow.arrow (𝔅 (Arrow.arrow (𝔅 σ) σ)) (𝔅 σ)) := by
  have hκ₁ : Provable₀ T₀ (Arrow.arrow (𝔅 (κ(σ))) (𝔅 σ)) := kreisel_specAux₁ σ;
  have : Provable₀ T₀ (Arrow.arrow (Arrow.arrow (𝔅 σ) σ) (Arrow.arrow (𝔅 κ(σ)) σ)) :=
    replace_imply_left! hκ₁;
  have : Provable₀ T (Arrow.arrow (Arrow.arrow (𝔅 σ) σ) κ(σ)) :=
    WeakerThan.pbl (𝓢 := T₀.alt) <| imp_trans''! this (kreisel_specAux₂ σ);
  exact imp_trans''! (mdp D2 (D1 this)) hκ₁;


-- @@ L390-390 verbatim
instance : 𝔅.FormalizedLoeb := ⟨formalized_loeb_theorem (T := T)⟩


-- @@ L392-392 verbatim
end «lp_section_7»


-- @@ L394-394 verbatim
variable [Entailment.Consistent T]


-- @@ L396-403 expanded
lemma _root_.LO.FirstOrder.DerivabilityCondition.unprovable_consistency_via_loeb [𝔅.Loeb] :
    Unprovable₀ T 𝔅.con := by
  by_contra hC; have : Provable₀ T ⊥ := Loeb.LT <| negEquiv'!.mp hC;
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <|
      inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction


-- @@ L405-405 expanded
variable [L.DecidableEq] [Diagonalization T₀] [WeakerThan T₀ T] [𝔅.HBL] [𝔅.GoedelSound]


-- @@ L407-412 expanded
lemma _root_.LO.FirstOrder.DerivabilityCondition.formalized_unprovable_not_consistency :
    Unprovable₀ T (Arrow.arrow 𝔅.con (Tilde.tilde (𝔅 (Tilde.tilde 𝔅.con)))) := by by_contra hC;
  have : Provable₀ T (Tilde.tilde 𝔅.con) := Loeb.LT <| contra₁'! hC;
  have : Unprovable₀ T (Tilde.tilde 𝔅.con) := unrefutable_consistency; contradiction;


-- @@ L414-421 expanded
lemma _root_.LO.FirstOrder.DerivabilityCondition.formalized_unrefutable_goedel :
    Unprovable₀ T (Arrow.arrow 𝔅.con (Tilde.tilde (𝔅 (Tilde.tilde 𝔅.goedel)))) := by by_contra hC;
  have : Unprovable₀ T (Arrow.arrow 𝔅.con (Tilde.tilde (𝔅 (Tilde.tilde 𝔅.con)))) :=
    formalized_unprovable_not_consistency;
  have : Provable₀ T (Arrow.arrow 𝔅.con (Tilde.tilde (𝔅 (Tilde.tilde 𝔅.con)))) :=
    imp_trans''! hC <|
      WeakerThan.pbl <|
        and₁'! <|
          neg_replace_iff'! <| prov_distribute_iff <| neg_replace_iff'! iff_goedel_consistency;
  contradiction;


-- @@ L423-423 verbatim
end «lp_section_5»


-- @@ L425-429 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.DerivabilityCondition.ProvabilityPredicate.rosser [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) : Sentence L :=
  fixpoint T₀ (Tilde.tilde (LO.FirstOrder.Rewriting.substitute 𝔅.prov (vecCons #0 ![])))


-- @@ L431-431 verbatim
section «lp_section_8»


-- @@ L433-433 verbatim
local notation "ρ" => 𝔅.rosser


-- @@ L435-435 verbatim
variable [Diagonalization T₀] [𝔅.Rosser]


-- @@ L437-438 expanded
omit [𝔅.Rosser] in
lemma _root_.LO.FirstOrder.DerivabilityCondition.rosser_spec :
    Provable₀ T₀ (LogicalConnective.iff ρ (Tilde.tilde (𝔅 ρ))) :=
  goedel_spec


-- @@ L440-440 verbatim
end «lp_section_8»


-- @@ L442-442 verbatim
section «lp_section_9»


-- @@ L444-444 expanded
variable [L.DecidableEq] [Diagonalization T₀] [WeakerThan T₀ T] [Entailment.Consistent T] [𝔅.Rosser]


-- @@ L446-446 verbatim
local notation "ρ" => 𝔅.rosser


-- @@ L448-449 expanded
omit [L.DecidableEq] [𝔅.Rosser] in
lemma _root_.LO.FirstOrder.DerivabilityCondition.unprovable_rosser : Unprovable₀ T ρ :=
  unprovable_goedel


-- @@ L451-458 expanded
omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.unrefutable_rosser :
    Unprovable₀ T (Tilde.tilde ρ) := by
  intro hnρ; have hρ : Provable₀ T ρ := WeakerThan.pbl <| mdp (and₂'! rosser_spec) (Ro hnρ);
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr <| by
  contradiction


-- @@ L460-466 expanded
omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.rosser_independent :
    Entailment.Undecidable T ↑ρ :=
  by
  suffices Unprovable₀ T ρ ∧ Unprovable₀ T (Tilde.tilde ρ) by
    simpa [Entailment.Undecidable, not_or, unprovable₀_iff] using this;
  constructor
  · apply unprovable_rosser
  · apply unrefutable_rosser


-- @@ L468-472 verbatim
omit [L.DecidableEq] in
theorem _root_.LO.FirstOrder.DerivabilityCondition.rosser_first_incompleteness
    (𝔅 : ProvabilityPredicate T₀ T) [𝔅.Rosser] :
    ¬Entailment.Complete T :=
  Entailment.incomplete_iff_exists_undecidable.mpr ⟨𝔅.rosser, rosser_independent  ⟩


-- @@ L474-474 verbatim
omit [Diagonalization T₀] [Consistent T]

-- @@ L475-479 expanded
omit [L.DecidableEq] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable in `T`. -/
theorem _root_.LO.FirstOrder.DerivabilityCondition.kriesel_remark : Provable₀ T 𝔅.con := by
  have : Provable₀ T₀ (Tilde.tilde (𝔅 ⊥)) := Ro (negEquiv'!.mpr (by simp));
  exact WeakerThan.pbl <| this;


-- @@ L481-481 verbatim
end «lp_section_9»


-- @@ L483-483 verbatim
end DerivabilityCondition


-- @@ L485-485 verbatim
end FirstOrder

-- @@ L486-486 verbatim
end LO
