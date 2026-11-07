/-
  ExecutionRequestsHashHashOne — pure + ambient for `erh_hash_one` under h_sha.

  Geometry (erhHashOne_prog 23 @ GuestAddrs.erh_hash_one = 0x8000c444):
    frame sp-16 save ra; la blob; SB type; copy body; JAL zkvm_sha256; epi.
  Non-ABI: x13=body, x14=type, x26=len, x24=dest.
  Residual: shaCallWithinShape at B1+76.
  Parent: #12011 option B.
-/
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.ExecutionRequestsHashShaResidual
import EvmAsm.Stateless.SpecRef.Crypto


-- @@ L22-22 verbatim
namespace EvmAsm.Codegen.ExecutionRequestsHashHashOne


-- @@ L24-24 verbatim
open EvmAsm.Rv64

-- @@ L25-25 verbatim
open EvmAsm.Codegen

-- @@ L26-26 verbatim
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual

-- @@ L27-27 verbatim
open EvmAsm.Stateless.SpecRef


-- @@ L29-29 verbatim
set_option maxRecDepth 8000


-- @@ L31-31 verbatim
abbrev B1 : Word := BitVec.ofNat 64 GuestAddrs.erh_hash_one

-- @@ L32-32 verbatim
abbrev Blob : Word := BitVec.ofNat 64 GuestAddrs.erh_blob

-- @@ L33-33 verbatim
abbrev hoProgL : List Instr := erhHashOne_prog


-- @@ L35-36 verbatim
theorem hoProgL_len : hoProgL.length = 23 := by
  simp only [hoProgL, erhHashOne_prog]; decide


-- @@ L38-39 verbatim
theorem hoProgL_bound : 4 * hoProgL.length < 2 ^ 64 := by
  rw [hoProgL_len]; norm_num


-- @@ L41-42 verbatim
private theorem shaProg_len : zkvmSha256_prog.length = 121 := by
  simp only [zkvmSha256_prog, zkvmSha256_prog_of]; decide


-- @@ L44-46 verbatim
/-- CodeReq covering erh_hash_one + zkvm_sha256 text. -/
def fullCodeHo : CodeReq :=
  (CodeReq.ofProg B1 hoProgL).union (CodeReq.ofProg ShaB zkvmSha256_prog)


-- @@ L48-54 verbatim
set_option maxRecDepth 8000 in
theorem wrapper_sha_disjoint :
    (CodeReq.ofProg B1 hoProgL).Disjoint (CodeReq.ofProg ShaB zkvmSha256_prog) := by
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [hoProgL_len]; decide
  · rw [shaProg_len]; decide
  · rw [hoProgL_len, shaProg_len]; decide


-- @@ L56-62 verbatim
theorem lift_ho {n : Nat} {entry exit_ : Word} {P Q : Assertion}
    (h : cpsTripleWithin n entry exit_ (CodeReq.ofProg B1 hoProgL) P Q) :
    cpsTripleWithin n entry exit_ fullCodeHo P Q :=
  cpsTripleWithin_extend_code
    (fun a i hi => by
      unfold fullCodeHo
      exact CodeReq.union_mono_left a i hi) h


-- @@ L64-72 verbatim
theorem mem_at (k : Nat) (ins : Instr) (pc : Word)
    (hpc : pc = B1 + BitVec.ofNat 64 (4 * k))
    (hk : k < hoProgL.length)
    (hins : hoProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton pc ins a = some i → fullCodeHo a = some i := by
  intro a i hs
  unfold fullCodeHo
  exact CodeReq.union_mono_left a i
    (CodeReq.ofProg_mem_at B1 pc hoProgL k ins hpc hk hins hoProgL_bound a i hs)


-- @@ L74-76 verbatim
/-- Pure blob payload: type byte ‖ body. -/
def hashOneBlob (typeB : BitVec 8) (body : List (BitVec 8)) : List (BitVec 8) :=
  typeB :: body


-- @@ L78-80 verbatim
theorem hashOneBlob_length (typeB : BitVec 8) (body : List (BitVec 8)) :
    (hashOneBlob typeB body).length = body.length + 1 := by
  simp [hashOneBlob]


-- @@ L82-84 verbatim
/-- Type byte from low 8 bits of typeW (guest SB truncates). -/
def typeByte (typeW : Word) : BitVec 8 :=
  BitVec.ofNat 8 typeW.toNat


-- @@ L86-87 verbatim
/-- PC of the residual JAL zkvm_sha256 inside erh_hash_one (idx 19). -/
def hashOneShaCallPc : Word := B1 + 76


-- @@ L89-90 verbatim
theorem hashOneShaCallPc_eq : hashOneShaCallPc = B1 + BitVec.ofNat 64 (4 * 19) := by
  simp only [hashOneShaCallPc]; decide


-- @@ L92-94 verbatim
/-- Residual offset at erh_hash_one+76. -/
def hashOneShaOff : BitVec 21 :=
  jalOff GuestAddrs.zkvm_sha256 (GuestAddrs.erh_hash_one + 76)


-- @@ L96-96 verbatim
end EvmAsm.Codegen.ExecutionRequestsHashHashOne
