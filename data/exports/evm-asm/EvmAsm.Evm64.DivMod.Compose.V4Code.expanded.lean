/-
  EvmAsm.Evm64.DivMod.Compose.V4Code

  Full DIV/MOD CodeReq bundles for the v4 div128 migration.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.V4NoNop
public import EvmAsm.Rv64.CPSSpec


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
open EvmAsm.Rv64.Tactics


-- @@ L16-16 verbatim
namespace EvmAsm.Evm64


-- @@ L18-18 verbatim
open EvmAsm.Rv64


-- @@ L20-39 verbatim
/-- v4 DIV code bundle matching the current `evm_div` program body. This keeps
    the legacy `divCode` surface stable while downstream migration proofs move
    to the full Knuth-D `divK_div128_v4` block. -/
abbrev divCode_v4 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24), -- block 10
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 11
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 12
    CodeReq.ofProg (base + div128Off)     divK_div128_v4          -- block 13
  ]


-- @@ L41-58 verbatim
/-- v4 MOD code bundle matching the current `evm_mod` program body. -/
abbrev modCode_v4 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]


-- @@ L60-68 verbatim
/-- v4 div128 block is included in the full DIV v4 code surface. -/
theorem div128_v4_ofProg_sub_divCode_v4 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128_v4) a = some i →
      (divCode_v4 base) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left


-- @@ L70-80 verbatim
/-- v4 div128 block is included in the full MOD v4 code surface. -/
theorem div128_v4_ofProg_sub_modCode_v4 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128_v4) a = some i →
      (modCode_v4 base) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left

-- Per-block bridge from the no-NOP v4 DIV surface to the full DIV v4 bundle.

-- @@ L81-83 verbatim
private theorem noNop_v4_b0_div {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L84-86 verbatim
private theorem noNop_v4_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left

-- @@ L87-89 verbatim
private theorem noNop_v4_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L90-92 verbatim
private theorem noNop_v4_b3_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L93-95 verbatim
private theorem noNop_v4_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L96-98 verbatim
private theorem noNop_v4_b5_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L99-101 verbatim
private theorem noNop_v4_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L102-104 verbatim
private theorem noNop_v4_b7_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L105-107 verbatim
private theorem noNop_v4_b8_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L108-110 verbatim
private theorem noNop_v4_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L111-113 verbatim
private theorem noNop_v4_b10_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L114-116 verbatim
private theorem noNop_v4_b11_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (divCode_v4 b) a = some i := by
  unfold divCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left


-- @@ L118-135 verbatim
/-- The DIV no-NOP v4 surface is included in the full DIV v4 code bundle. -/
theorem divCode_noNop_v4_sub_divCode_v4 {base : Word} :
    ∀ a i, (divCode_noNop_v4 base) a = some i → (divCode_v4 base) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono noNop_v4_b0_div
    (CodeReq.union_split_mono noNop_v4_b1_div
    (CodeReq.union_split_mono noNop_v4_b2_div
    (CodeReq.union_split_mono noNop_v4_b3_div
    (CodeReq.union_split_mono noNop_v4_b4_div
    (CodeReq.union_split_mono noNop_v4_b5_div
    (CodeReq.union_split_mono noNop_v4_b6_div
    (CodeReq.union_split_mono noNop_v4_b7_div
    (CodeReq.union_split_mono noNop_v4_b8_div
    (CodeReq.union_split_mono noNop_v4_b9_div
    (CodeReq.union_split_mono noNop_v4_b10_div
    (CodeReq.union_split_mono noNop_v4_b11_div
    (CodeReq.union_split_mono div128_v4_ofProg_sub_divCode_v4
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))


-- @@ L137-144 verbatim
/-- Lift a DIV proof over the no-NOP v4 code surface to the full v4 bundle. -/
theorem cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    {nSteps : Nat} {entry exit_ base : Word} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ (divCode_noNop_v4 base) P Q) :
    cpsTripleWithin nSteps entry exit_ (divCode_v4 base) P Q := by
  exact cpsTripleWithin_extend_code (hmono := divCode_noNop_v4_sub_divCode_v4) h

-- Per-block bridge from the no-NOP v4 MOD surface to the full MOD v4 bundle.

-- @@ L145-147 verbatim
private theorem noNop_v4_b0_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left

-- @@ L148-150 verbatim
private theorem noNop_v4_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left

-- @@ L151-153 verbatim
private theorem noNop_v4_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L154-156 verbatim
private theorem noNop_v4_b3_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L157-159 verbatim
private theorem noNop_v4_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L160-162 verbatim
private theorem noNop_v4_b5_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L163-165 verbatim
private theorem noNop_v4_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L166-168 verbatim
private theorem noNop_v4_b7_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L169-171 verbatim
private theorem noNop_v4_b8_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L172-174 verbatim
private theorem noNop_v4_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L175-177 verbatim
private theorem noNop_v4_b10_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

-- @@ L178-180 verbatim
private theorem noNop_v4_b11_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (modCode_v4 b) a = some i := by
  unfold modCode_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left


-- @@ L182-199 verbatim
/-- The MOD no-NOP v4 surface is included in the full MOD v4 code bundle. -/
theorem modCode_noNop_v4_sub_modCode_v4 {base : Word} :
    ∀ a i, (modCode_noNop_v4 base) a = some i → (modCode_v4 base) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono noNop_v4_b0_mod
    (CodeReq.union_split_mono noNop_v4_b1_mod
    (CodeReq.union_split_mono noNop_v4_b2_mod
    (CodeReq.union_split_mono noNop_v4_b3_mod
    (CodeReq.union_split_mono noNop_v4_b4_mod
    (CodeReq.union_split_mono noNop_v4_b5_mod
    (CodeReq.union_split_mono noNop_v4_b6_mod
    (CodeReq.union_split_mono noNop_v4_b7_mod
    (CodeReq.union_split_mono noNop_v4_b8_mod
    (CodeReq.union_split_mono noNop_v4_b9_mod
    (CodeReq.union_split_mono noNop_v4_b10_mod
    (CodeReq.union_split_mono noNop_v4_b11_mod
    (CodeReq.union_split_mono div128_v4_ofProg_sub_modCode_v4
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))


-- @@ L201-206 verbatim
/-- Lift a MOD proof over the no-NOP v4 code surface to the full v4 bundle. -/
theorem cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    {nSteps : Nat} {entry exit_ base : Word} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ (modCode_noNop_v4 base) P Q) :
    cpsTripleWithin nSteps entry exit_ (modCode_v4 base) P Q := by
  exact cpsTripleWithin_extend_code (hmono := modCode_noNop_v4_sub_modCode_v4) h


-- @@ L208-208 verbatim
end EvmAsm.Evm64
