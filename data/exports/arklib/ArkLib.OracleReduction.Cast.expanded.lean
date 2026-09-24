/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.ProtocolSpec.Cast
public import ArkLib.OracleReduction.Security.RoundByRound


-- @@ L11-29 verbatim
/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DCast` instances) for the following structures:
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`

  Note that casting for `ProtocolSpec`s and related structures are defined in
  `OracleReduction/ProtocolSpec/Cast.lean`.

  We also show that casting preserves execution (up to casting of the transcripts) and thus security
  properties.

  **Verified vs. admitted.** The *execution* lemmas (including the oracle-side
  `OracleVerifier.cast_toVerifier`) and the round-by-round knowledge-soundness transfer
  (`Verifier.cast_rbrKnowledgeSoundness` and its oracle-side corollary) are proven. The
  completeness transfer lemmas are commented out entirely and remain future work.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
open OracleComp


-- @@ L35-41 verbatim
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n₁ n₂ : ℕ} {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}
  (hn : n₁ = n₂) (hSpec : pSpec₁.cast hn = pSpec₂)


-- @@ L43-43 verbatim
open ProtocolSpec


-- @@ L45-45 verbatim
namespace Prover


-- @@ L47-58 verbatim
/-- Casting the prover of a non-oracle reduction across an equality of `ProtocolSpec`s. -/
protected def cast (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  PrvState := P.PrvState ∘ Fin.cast (congrArg (· + 1) hn.symm)
  input := P.input
  sendMessage := fun i st => do
    let ⟨msg, newSt⟩ ← P.sendMessage (i.cast hn.symm (cast_symm hSpec)) st
    return ⟨(Message.cast_idx_symm hSpec) ▸ msg, newSt⟩
  receiveChallenge := fun i st => do
    let f ← P.receiveChallenge (i.cast hn.symm (cast_symm hSpec)) st
    return fun chal => f (Challenge.cast_idx hSpec ▸ chal)
  output := P.output ∘ (fun st => _root_.cast (by simp) st)


-- @@ L60-73 verbatim
@[simp]
theorem cast_id :
    Prover.cast rfl rfl = (id : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext
  unfold Prover.cast
  simp only [ProtocolSpec.cast_id, id_eq]
  ext <;> simp only [MessageIdx, Function.comp_apply, Fin.cast_eq_self, Message,
    ChallengeIdx, Challenge, cast_eq, bind_pure_comp, heq_eq_eq]
  · funext _ _
    simp [MessageIdx.cast]
  · apply heq_of_eq
    funext _ _
    simp [ChallengeIdx.cast]
  · rfl


-- @@ L75-78 verbatim
instance instDCast₂ : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Prover.cast
  dcast₂_id := Prover.cast_id


-- @@ L80-80 verbatim
end Prover


-- @@ L82-82 verbatim
namespace OracleProver


-- @@ L84-89 verbatim
/-- Casting the oracle prover of a non-oracle reduction across an equality of `ProtocolSpec`s.

Internally invokes the `Prover.cast` function. -/
protected def cast (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ :=
  Prover.cast hn hSpec P


-- @@ L91-96 verbatim
omit Oₛᵢ Oₛₒ in
@[simp]
theorem cast_id :
    OracleProver.cast rfl rfl =
      (id : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
  exact Prover.cast_id


-- @@ L98-101 verbatim
instance instDCast₂OracleProver : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) where
  dcast₂ := OracleProver.cast
  dcast₂_id := OracleProver.cast_id


-- @@ L103-103 verbatim
end OracleProver


-- @@ L105-105 verbatim
namespace Verifier


-- @@ L107-112 verbatim
/-- Casting the verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

This boils down to casting the (full) transcript. -/
protected def cast (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) transcript)


-- @@ L114-116 verbatim
@[simp]
theorem cast_id : Verifier.cast rfl rfl = (id : Verifier oSpec StmtIn StmtOut pSpec₁ → _) := by
  ext; simp [Verifier.cast]


-- @@ L118-121 verbatim
instance instDCast₂Verifier :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp [Verifier.cast]


-- @@ L123-124 verbatim
theorem cast_eq_dcast₂ {V : Verifier oSpec StmtIn StmtOut pSpec₁} :
    V.cast hn hSpec = dcast₂ hn hSpec V := rfl


-- @@ L126-126 verbatim
end Verifier


-- @@ L128-128 verbatim
namespace OracleVerifier


-- @@ L130-131 verbatim
variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]


-- @@ L133-156 verbatim
/-- Casting the oracle verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

TODO: need a cast of the oracle interfaces as well (i.e. the oracle interface instance is not
necessarily unique for every type) -/
protected def cast
    (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₂ := by
  cases hn
  rw [show pSpec₁.cast rfl = pSpec₁ from rfl] at hSpec
  cases hSpec
  have hs : hSpec = rfl := Subsingleton.elim _ _
  cases hs
  have hInterfaces : Oₘ₁ = Oₘ₂ := by
    funext i
    have hi : i.cast rfl rfl = i := by
      apply Subtype.ext
      rfl
    have h := hOₘ i
    cases hi
    simpa [MessageIdx.cast, Message.cast_idx, ProtocolSpec.cast_Type_idx,
      dcast_eq_root_cast, ProtocolSpec.cast] using h
  subst hInterfaces
  exact V


-- @@ L158-170 verbatim
variable (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

-- @[simp]
-- theorem cast_id :
--     OracleVerifier.cast rfl rfl (fun i => rfl) =
--       (id : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁ → _) := by
--   sorry

-- Need to cast oracle interface as well
-- instance instDCast₂OracleVerifier : DCast₃ Nat ProtocolSpec
--     (fun _ pSpec => OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) where
--   dcast₂ := OracleVerifier.cast
--   dcast₂_id := OracleVerifier.cast_id


-- @@ L172-190 verbatim
@[simp]
theorem cast_toVerifier (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    (OracleVerifier.cast hn hSpec hOₘ V).toVerifier = Verifier.cast hn hSpec V.toVerifier := by
  cases hn
  rw [show pSpec₁.cast rfl = pSpec₁ from rfl] at hSpec
  cases hSpec
  have hs : hSpec = rfl := Subsingleton.elim _ _
  cases hs
  have hInterfaces : Oₘ₁ = Oₘ₂ := by
    funext i
    have hi : i.cast rfl rfl = i := by
      apply Subtype.ext
      rfl
    have h := hOₘ i
    cases hi
    simpa [MessageIdx.cast, Message.cast_idx, ProtocolSpec.cast_Type_idx,
      dcast_eq_root_cast, ProtocolSpec.cast] using h
  subst hInterfaces
  rfl


-- @@ L192-192 verbatim
end OracleVerifier


-- @@ L194-194 verbatim
namespace Reduction


-- @@ L196-201 verbatim
/-- Casting the reduction of a non-oracle reduction across an equality of `ProtocolSpec`s, which
  casts the underlying prover and verifier. -/
protected def cast (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec


-- @@ L203-209 verbatim
@[simp]
theorem cast_id :
    Reduction.cast rfl rfl = (id : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext x
  simp only [Reduction.cast, id]
  congr 1
  exact congr_fun (Prover.cast_id (pSpec₁ := pSpec₁)) _


-- @@ L211-214 verbatim
instance instDCast₂Reduction :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Reduction.cast
  dcast₂_id := Reduction.cast_id


-- @@ L216-216 verbatim
end Reduction


-- @@ L218-218 verbatim
namespace OracleReduction


-- @@ L220-222 verbatim
variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))


-- @@ L224-243 verbatim
/-- Casting the oracle reduction across an equality of `ProtocolSpec`s, which casts the underlying
  prover and verifier. -/
protected def cast (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec hOₘ

-- @[simp]
-- theorem cast_id :
--     OracleReduction.cast rfl rfl (fun _ => rfl) =
--       (id : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
--   ext : 2 <;> simp [OracleReduction.cast]

-- Need to cast oracle interface as well
-- instance instDCast₂OracleReduction :
--     DCast₂ Nat ProtocolSpec
--     (fun _ pSpec => OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
-- where
--   dcast₂ := OracleReduction.cast
--   dcast₂_id := OracleReduction.cast_id


-- @@ L245-249 verbatim
@[simp]
theorem cast_toReduction
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    (R.cast hn hSpec hOₘ).toReduction = Reduction.cast hn hSpec R.toReduction := by
  simp [OracleReduction.cast, Reduction.cast, OracleReduction.toReduction, OracleProver.cast]


-- @@ L251-251 verbatim
end OracleReduction


-- @@ L253-255 verbatim
section Execution

-- TODO: show that the execution of everything is the same, modulo casting of transcripts

-- @@ L256-256 verbatim
variable {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂} (hSpec : pSpec₁.cast hn = pSpec₂)


-- @@ L258-261 verbatim
namespace Prover

-- TODO: need to cast [pSpec₁.Challenge]ₒ to [pSpec₂.Challenge]ₒ, where they have the default
-- instance `challengeOracleInterface`


-- @@ L263-281 verbatim
theorem cast_processRound (j : Fin n₁)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁)
    (currentResult : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (Transcript j.castSucc pSpec₁ × P.PrvState j.castSucc)) :
    P.processRound j currentResult =
      cast (by subst_vars; simp [Prover.cast]; rfl)
        ((P.cast hn hSpec).processRound (Fin.cast hn j)
          (cast (by subst_vars; simp [Prover.cast]; rfl) currentResult)) := by
  subst hn; subst hSpec; congr 1
  unfold Prover.cast
  ext <;> simp only [MessageIdx, Function.comp_apply, Fin.cast_eq_self, Message,
    ChallengeIdx, Challenge, cast_eq, bind_pure_comp, heq_eq_eq]
  · apply heq_of_eq
    funext _ _
    simp [MessageIdx.cast]
  · apply heq_of_eq
    funext _ _
    simp [ChallengeIdx.cast]
  · rfl


-- @@ L283-298 verbatim
theorem cast_runToRound (j : Fin (n₁ + 1)) (stmt : StmtIn) (wit : WitIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    P.runToRound j stmt wit =
      cast (by subst_vars; simp [Prover.cast]; rfl)
        ((P.cast hn hSpec).runToRound (Fin.cast (congrArg (· + 1) hn) j) stmt wit) := by
  subst hn; subst hSpec; congr 1
  unfold Prover.cast
  ext <;> simp only [MessageIdx, Function.comp_apply, Fin.cast_eq_self, Message,
    ChallengeIdx, Challenge, cast_eq, bind_pure_comp, heq_eq_eq]
  · apply heq_of_eq
    funext _ _
    simp [MessageIdx.cast]
  · apply heq_of_eq
    funext _ _
    simp [ChallengeIdx.cast]
  · rfl


-- @@ L300-304 verbatim
theorem cast_run (stmt : StmtIn) (wit : WitIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    P.run stmt wit =
      cast (by subst_vars; simp; rfl) ((P.cast hn hSpec).run stmt wit) := by
  subst hn; subst hSpec; simp only [Prover.cast_id, id_eq]; rfl


-- @@ L306-306 verbatim
end Prover


-- @@ L308-308 verbatim
namespace Verifier


-- @@ L310-310 verbatim
variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)


-- @@ L312-318 verbatim
/-- The casted verifier produces the same output as the original verifier. -/
@[simp]
theorem cast_run (stmt : StmtIn) (transcript : FullTranscript pSpec₁) :
    V.run stmt transcript = (V.cast hn hSpec).run stmt (transcript.cast hn hSpec) := by
  cases hn
  cases hSpec
  rfl


-- @@ L320-320 verbatim
end Verifier


-- @@ L322-322 verbatim
namespace Reduction


-- @@ L324-324 verbatim
variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)


-- @@ L326-329 verbatim
theorem cast_run (stmt : StmtIn) (wit : WitIn) :
    R.run stmt wit =
      cast (by subst_vars; simp; rfl) ((R.cast hn hSpec).run stmt wit) := by
  subst hn; subst hSpec; simp only [Reduction.cast_id, id_eq]; rfl


-- @@ L331-331 verbatim
end Reduction


-- @@ L333-333 verbatim
end Execution


-- @@ L335-335 verbatim
section Security


-- @@ L337-337 verbatim
open NNReal


-- @@ L339-342 verbatim
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [inst₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
  [inst₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]
  (hChallenge : ∀ i, inst₁ i = dcast (by simp) (inst₂ (i.cast hn hSpec)))


-- @@ L344-344 verbatim
section Protocol


-- @@ L346-346 verbatim
variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}


-- @@ L348-348 verbatim
namespace Reduction


-- @@ L350-360 verbatim
variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

-- @[simp]
-- theorem cast_completeness (ε : ℝ≥0) (hComplete : R.completeness init impl relIn relOut ε) :
--     (R.cast hn hSpec).completeness init impl relIn relOut ε := by
--   sorry

-- @[simp]
-- theorem cast_perfectCompleteness (hComplete : R.perfectCompleteness init impl relIn relOut) :
--     (R.cast hn hSpec).perfectCompleteness init impl relIn relOut :=
--   cast_completeness hn hSpec R 0 hComplete


-- @@ L362-362 verbatim
end Reduction


-- @@ L364-364 verbatim
namespace Verifier


-- @@ L366-366 verbatim
variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)


-- @@ L368-448 verbatim
/-- Round-by-round knowledge soundness transfers across a `ProtocolSpec` cast.
This is the base case that `OracleVerifier.cast_rbrKnowledgeSoundness` reduces to. -/
@[simp]
theorem cast_rbrKnowledgeSoundness (ε : pSpec₁.ChallengeIdx → ℝ≥0)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (V.cast hn hSpec).rbrKnowledgeSoundness init impl relIn relOut
      (ε ∘ (ChallengeIdx.cast hn.symm (cast_symm hSpec))) := by
  -- After `subst`, the cast is definitionally trivial and the only residual difference is the
  -- `Finite` instance on each challenge type; `uniformSample`'s distribution is
  -- instance-irrelevant, so the two games have equal `evalSPMF` and the bound transports.
  subst hn
  simp only [ProtocolSpec.cast_id, id_eq] at hSpec
  subst hSpec
  change @rbrKnowledgeSoundness ι oSpec StmtIn WitIn StmtOut WitOut n₁ pSpec₁ inst₂ σ
    init impl relIn relOut V ε
  have hhandler : ∀ (t : (oSpec + [pSpec₁.Challenge]ₒ).Domain) (s : σ),
      𝒮[((impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₁) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) t).run s] =
      𝒮[((impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₂) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) t).run s] := by
    intro t s
    cases t with
    | inl t => rfl
    | inr t =>
      rcases t with ⟨i, q⟩
      cases q
      have huni :
          𝒮[@uniformSample (pSpec₁.Challenge i) (inst₁ i)] =
          𝒮[@uniformSample (pSpec₁.Challenge i) (inst₂ i)] := by
        let : Fintype (pSpec₁.Challenge i) := Fintype.ofFinite _
        apply evalSPMF_ext
        intro x
        exact (@probOutput_uniformSample (pSpec₁.Challenge i) (inst₁ i) this x).trans
          (@probOutput_uniformSample (pSpec₁.Challenge i) (inst₂ i) this x).symm
      change
        𝒮[(liftM (@uniformSample (pSpec₁.Challenge i) (inst₁ i)) :
            StateT σ ProbComp (pSpec₁.Challenge i)).run s] =
        𝒮[(liftM (@uniformSample (pSpec₁.Challenge i) (inst₂ i)) :
            StateT σ ProbComp (pSpec₁.Challenge i)).run s]
      rw [OracleComp.liftM_run_StateT, OracleComp.liftM_run_StateT]
      rw [evalSPMF_bind, evalSPMF_bind]
      exact congrArg
        (fun d : SPMF (pSpec₁.Challenge i) =>
          d >>= fun x => 𝒮[(pure (x, s) : ProbComp (pSpec₁.Challenge i × σ))]) huni
  have hsim : ∀ {α : Type} (oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) (s : σ),
      𝒮[(simulateQ (impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₁) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) oa).run s] =
      𝒮[(simulateQ (impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₂) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) oa).run s] := by
    intro α oa s
    exact evalSPMF_simulateQ_run_congr _ _ hhandler oa s
  unfold rbrKnowledgeSoundness at hRbrKs ⊢
  obtain ⟨WitMid, extractor, kSF, hbound⟩ := hRbrKs
  refine ⟨WitMid, extractor, kSF, ?_⟩
  intro stmtIn witIn prover i
  let game := do
    let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
    let challenge ← (pSpec₁.getChallenge i).liftComp (oSpec + [pSpec₁.Challenge]ₒ)
    return (transcript, challenge, proveQueryLog)
  have hrun (s : σ) :
      𝒮[(simulateQ (impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₁) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) game).run' s] =
      𝒮[(simulateQ (impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₂) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) game).run' s] := by
    simp only [StateT.run'_eq, evalSPMF_map]
    exact congrArg (Functor.map Prod.fst) (hsim game s)
  have heval :
      𝒮[(do
        let s ← init
        (simulateQ (impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₂) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) game).run' s)] =
      𝒮[(do
        let s ← init
        (simulateQ (impl.addLift (@challengeQueryImpl n₁ pSpec₁ inst₁) :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) game).run' s)] := by
    rw [evalSPMF_bind, evalSPMF_bind]
    apply bind_congr
    intro s
    exact (hrun s).symm
  exact (probEvent_congr' (fun _ _ => Iff.rfl) heval).trans_le
    (hbound stmtIn witIn prover i)


-- @@ L450-450 verbatim
end Verifier


-- @@ L452-452 verbatim
end Protocol


-- @@ L454-454 verbatim
section OracleProtocol


-- @@ L456-460 verbatim
variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}


-- @@ L462-462 verbatim
namespace OracleReduction


-- @@ L464-476 verbatim
variable (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁)

-- @[simp]
-- theorem cast_completeness (ε : ℝ≥0) (hComplete : R.completeness init impl relIn relOut ε) :
--     (R.cast hn hSpec hOₘ).completeness init impl relIn relOut ε := by
--   unfold completeness
--   rw [cast_toReduction]
--   exact Reduction.cast_completeness hn hSpec R.toReduction ε hComplete

-- @[simp]
-- theorem cast_perfectCompleteness (hComplete : R.perfectCompleteness init impl relIn relOut) :
--     (R.cast hn hSpec hOₘ).perfectCompleteness init impl relIn relOut :=
--   cast_completeness hn hSpec hOₘ R 0 hComplete


-- @@ L478-478 verbatim
end OracleReduction


-- @@ L480-480 verbatim
namespace OracleVerifier


-- @@ L482-482 verbatim
variable (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁)


-- @@ L484-493 verbatim
/-- Round-by-round knowledge soundness transfers across a `ProtocolSpec` cast, on the oracle
side; reduces to `Verifier.cast_rbrKnowledgeSoundness`. -/
@[simp]
theorem cast_rbrKnowledgeSoundness (ε : pSpec₁.ChallengeIdx → ℝ≥0)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (V.cast hn hSpec hOₘ).rbrKnowledgeSoundness init impl relIn relOut
      (ε ∘ (ChallengeIdx.cast hn.symm (cast_symm hSpec))) := by
  unfold rbrKnowledgeSoundness
  rw [cast_toVerifier]
  exact Verifier.cast_rbrKnowledgeSoundness hn hSpec V.toVerifier ε hRbrKs


-- @@ L495-495 verbatim
end OracleVerifier


-- @@ L497-497 verbatim
end OracleProtocol


-- @@ L499-499 verbatim
end Security
