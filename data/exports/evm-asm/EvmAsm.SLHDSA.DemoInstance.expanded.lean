/-
  EvmAsm.SLHDSA.DemoInstance

  A concrete, RV64-friendly instantiation of the SLH-DSA primitive bundle
  (`SLHDSA.Primitives`): every carrier is a 64-bit word and every hash /
  PRF is built from one word-mixing step `mix h x = (h ^^^ x) * K`, which
  is exactly two RV64 instructions (XOR + MUL).  The parameter set
  `demoParams` is a deliberately tiny demonstration set (n = 1 byte nodes,
  single-layer hypertree of height 1, two FORS trees of height 1,
  Winternitz w = 2) so the whole verifier unrolls to straight-line RV64
  code; it exercises every algorithmic component of FIPS 205 verification
  (H_msg digest split, FORS leaf recovery and auth-path climb, the WOTS+
  message+checksum digit vector, per-chain completion, T_len compression,
  XMSS auth-path climb, root comparison) but is NOT a FIPS 205 security
  parameter set — the primitives are trivially non-cryptographic mixers.

  `demoVerifyWords` is the word-level reference verifier written exactly
  as the RV64 code computes (one `let` per intermediate register value);
  `DemoCorrect.lean` proves it equal to the ported specification
  `SLHDSA.slhVerifyInternal demoPrims`, and the SAsm proof
  (`EvmAsm.SLHDSA.VerifySAsm`) shows the machine code computes
  `demoVerifyWords`.
-/

module
public import EvmAsm.SLHDSA.Scheme


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace SLHDSA

-- @@ L31-31 verbatim
namespace Demo


-- @@ L33-33 verbatim
/-! ## The word mixer and domain constants -/


-- @@ L35-41 verbatim
/-- One mixing step: absorb `x` into the state `h`.  A single RV64 `ADD`.
This demonstration mixer is deliberately linear (hence trivially not
collision-resistant); SLH-DSA *correctness* (`verify ∘ sign = accept`)
holds for any choice of the opaque hash primitives, so a one-instruction
mixer keeps the verified RV64 code small while exercising every
algorithmic component of FIPS 205 verification. -/
def mix (h x : BitVec 64) : BitVec 64 := h + x


-- @@ L43-44 verbatim
/-- Domain constant of the address digest. -/
def adrsC : BitVec 64 := 0xA0A0A0A0A0A0A0A1

-- @@ L45-46 verbatim
/-- Domain constant of `F`. -/
def fC : BitVec 64 := 0xF0F0F0F0F0F0F0F1

-- @@ L47-48 verbatim
/-- Domain constant of `H`. -/
def hC : BitVec 64 := 0xB0B0B0B0B0B0B0B1

-- @@ L49-50 verbatim
/-- Domain constant of `T_ℓ`. -/
def tC : BitVec 64 := 0xC0C0C0C0C0C0C0C1

-- @@ L51-52 verbatim
/-- Domain constant of `PRF`. -/
def pC : BitVec 64 := 0xD0D0D0D0D0D0D0D1

-- @@ L53-54 verbatim
/-- Domain constant of `PRF_msg`. -/
def rC : BitVec 64 := 0xE0E0E0E0E0E0E0E1

-- @@ L55-56 verbatim
/-- Domain constant of `H_msg`. -/
def mC : BitVec 64 := 0x1010101010101011


-- @@ L58-63 verbatim
/-- The 64-bit digest of a 32-byte address: absorb the six conceptual
words in order. -/
def adrsVal (a : Adrs) : BitVec 64 :=
  mix (mix (mix (mix (mix (mix adrsC (BitVec.ofNat 64 a.layer)) (BitVec.ofNat 64 a.tree))
    (BitVec.ofNat 64 a.type)) (BitVec.ofNat 64 a.word1)) (BitVec.ofNat 64 a.word2))
    (BitVec.ofNat 64 a.word3)


-- @@ L65-69 verbatim
/-- The address digest for `layer = tree = 0` addresses, with the three
type-dependent words already as runtime words — the shape every address
of the `d = 1` verifier takes. -/
def adrsW (ty : ℕ) (w1 w2 w3 : BitVec 64) : BitVec 64 :=
  mix (mix (mix (mix (mix (mix adrsC 0) 0) (BitVec.ofNat 64 ty)) w1) w2) w3


-- @@ L71-73 verbatim
theorem adrsVal_eq_adrsW (ty n1 n2 n3 : ℕ) :
    adrsVal ⟨0, 0, ty, n1, n2, n3⟩
      = adrsW ty (BitVec.ofNat 64 n1) (BitVec.ofNat 64 n2) (BitVec.ofNat 64 n3) := rfl


-- @@ L75-76 verbatim
/-- The word computation of `F`. -/
def fW (pk adr m : BitVec 64) : BitVec 64 := mix (mix (mix fC pk) adr) m


-- @@ L78-79 verbatim
/-- The word computation of `H`. -/
def hW (pk adr l r : BitVec 64) : BitVec 64 := mix (mix (mix (mix hC pk) adr) l) r


-- @@ L81-82 verbatim
/-- The initial `T_ℓ` state, before absorbing the message blocks. -/
def tlInit (pk adr : BitVec 64) : BitVec 64 := mix (mix tC pk) adr


-- @@ L84-87 verbatim
/-- The word digest inside `H_msg` (the two digest bytes are its bits
15–8 and 7–0). -/
def hmsgW (r pk root msgW : BitVec 64) : BitVec 64 :=
  mix (mix (mix (mix mC r) pk) root) msgW


-- @@ L89-89 verbatim
/-! ## The demonstration parameter set and primitive bundle -/


-- @@ L91-95 verbatim
/-- The demonstration parameter set: 1-byte nodes, a single XMSS layer of
height 1, two FORS trees of height 1, `w = 2`.  Derived lengths:
`len1 = 8`, `len2 = 4`, `len = 12`, `m = 2`. -/
def demoParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 1, k := 2, lgw := 1 }


-- @@ L97-97 verbatim
theorem demoParams_len1 : demoParams.len1 = 8 := rfl


-- @@ L99-103 verbatim
theorem demoParams_len2 : demoParams.len2 = 4 := by
  show Nat.log 2 (demoParams.len1 * (demoParams.w - 1)) + 1 = 4
  rw [demoParams_len1]
  rw [show demoParams.w - 1 = 1 from rfl]
  rw [show 8 * 1 = 2 ^ 3 from rfl, Nat.log_pow (by omega)]


-- @@ L105-107 verbatim
theorem demoParams_len : demoParams.len = 12 := by
  show demoParams.len1 + demoParams.len2 = 12
  rw [demoParams_len1, demoParams_len2]


-- @@ L109-109 verbatim
theorem demoParams_m : demoParams.m = 2 := rfl


-- @@ L111-128 verbatim
/-- The demonstration primitive bundle: all carriers are `BitVec 64`,
all six functions are `mix` chains under distinct domain constants.
`Hmsg` serializes the low 16 bits of its word digest big-endian;
`yToBytes` takes the node's low byte. -/
def demoPrims : Primitives demoParams where
  PkSeed := BitVec 64
  SkSeed := BitVec 64
  SkPrf := BitVec 64
  Y := BitVec 64
  F := fun pk a m => fW pk (adrsVal a) m
  H := fun pk a l r => hW pk (adrsVal a) l r
  Tl := fun pk a ms => ms.foldl mix (tlInit pk (adrsVal a))
  PRF := fun pk sk a => mix (mix (mix pC pk) sk) (adrsVal a)
  PRFmsg := fun kp rnd m => mix (mix (mix rC kp) rnd) (BitVec.ofNat 64 (toInt m))
  Hmsg := fun r pk root m =>
    let d := hmsgW r pk root (BitVec.ofNat 64 (toInt m))
    ⟨#[UInt8.ofNat (d.toNat >>> 8 % 256), UInt8.ofNat (d.toNat % 256)], rfl⟩
  yToBytes := fun y => ⟨#[UInt8.ofNat (y.toNat % 256)], rfl⟩


-- @@ L130-131 verbatim
instance : DecidableEq demoPrims.Y :=
  inferInstanceAs (DecidableEq (BitVec 64))


-- @@ L133-133 verbatim
/-! ## The word-level input format -/


-- @@ L135-154 verbatim
/-- The signature, as the fixed-size vector of 64-bit words the RV64
verifier reads: the randomizer, per FORS tree the revealed leaf secret
and its single auth node, the twelve WOTS+ chain values, and the single
XMSS auth node — 19 words, mirroring the fixed-size FIPS 205 signature
layout `R ‖ SIG_FORS ‖ SIG_HT`. -/
structure SigWords where
  /-- The randomizer `R`. -/
  r : BitVec 64
  /-- FORS tree 0: revealed leaf secret. -/
  s0 : BitVec 64
  /-- FORS tree 0: the auth-path node. -/
  a0 : BitVec 64
  /-- FORS tree 1: revealed leaf secret. -/
  s1 : BitVec 64
  /-- FORS tree 1: the auth-path node. -/
  a1 : BitVec 64
  /-- The twelve WOTS+ signature chain values. -/
  w : Fin 12 → BitVec 64
  /-- The XMSS auth-path node. -/
  xa : BitVec 64


-- @@ L156-160 verbatim
/-- The specification-level signature carried by a `SigWords` input. -/
def SigWords.toSig (s : SigWords) : Signature demoPrims :=
  (s.r,
   ⟨#[(s.s0, [s.a0]), (s.s1, [s.a1])], rfl⟩,
   (Vector.ofFn fun j : Fin demoParams.len => s.w (Fin.cast demoParams_len j), [s.xa]))


-- @@ L162-162 verbatim
/-! ## The word-level reference verifier -/


-- @@ L164-168 verbatim
/-- The WOTS+ digit of chain `i` as the RV64 code computes it: bits of
the committed byte `mb` (most significant first) for `i < 8`, bits of
the checksum `csum` for the last four chains. -/
def digitW (mb csum : BitVec 64) (i : ℕ) : BitVec 64 :=
  if i < 8 then (mb >>> (7 - i)) &&& 1 else (csum >>> (11 - i)) &&& 1


-- @@ L170-174 verbatim
/-- The completed top of WOTS+ chain `i`: the signature value itself when
the digit is 1 (already at the chain top for `w = 2`), one `F` step at
hash address 0 otherwise. -/
def chainTopW (pkSeed idxLeaf : BitVec 64) (i : ℕ) (d wi : BitVec 64) : BitVec 64 :=
  if d = 1 then wi else fW pkSeed (adrsW 0 idxLeaf (BitVec.ofNat 64 i) 0) wi


-- @@ L176-210 verbatim
/-- The word-level reference verifier, written exactly as the RV64 code
computes: every `let` is one intermediate register value.  `msgW` is the
message packed big-endian into one word (`BitVec.ofNat 64 (toInt msg)`),
which is all of the message the demonstration `H_msg` absorbs. -/
def demoVerifyWords (pkSeed pkRoot msgW : BitVec 64) (s : SigWords) : Bool :=
  -- message digest and its split
  let hm := hmsgW s.r pkSeed pkRoot msgW
  let idxLeaf := hm &&& 1
  -- FORS leaf indices: the top two bits of the digest's first byte
  let f0 := (hm >>> 15) &&& 1
  let f1 := (hm >>> 14) &&& 1
  -- FORS tree 0: recompute the leaf, climb the single auth level
  let leaf0 := fW pkSeed (adrsW 3 idxLeaf 0 f0) s.s0
  let root0 := if f0 = 0 then hW pkSeed (adrsW 3 idxLeaf 1 0) leaf0 s.a0
               else hW pkSeed (adrsW 3 idxLeaf 1 0) s.a0 leaf0
  -- FORS tree 1 (global leaf index 2 + f1)
  let leaf1 := fW pkSeed (adrsW 3 idxLeaf 0 (2 + f1)) s.s1
  let root1 := if f1 = 0 then hW pkSeed (adrsW 3 idxLeaf 1 1) leaf1 s.a1
               else hW pkSeed (adrsW 3 idxLeaf 1 1) s.a1 leaf1
  -- the FORS public key: T_k over the two recovered roots
  let forsPk := mix (mix (tlInit pkSeed (adrsW 4 idxLeaf 0 0)) root0) root1
  -- WOTS+ digits: the committed byte, its bit-sum, and the checksum
  let mb := forsPk &&& 0xff
  let dsum := ((mb >>> 7) &&& 1) + ((mb >>> 6) &&& 1) + ((mb >>> 5) &&& 1)
    + ((mb >>> 4) &&& 1) + ((mb >>> 3) &&& 1) + ((mb >>> 2) &&& 1)
    + ((mb >>> 1) &&& 1) + (mb &&& 1)
  let csum := 8 - dsum
  -- complete the twelve chains and compress with T_len
  let leafPk := (List.ofFn fun i : Fin 12 =>
    chainTopW pkSeed idxLeaf i.val (digitW mb csum i.val) (s.w i)).foldl mix
    (tlInit pkSeed (adrsW 1 idxLeaf 0 0))
  -- the XMSS auth-path climb (height 1) and the root comparison
  let root := if idxLeaf = 0 then hW pkSeed (adrsW 2 0 1 0) leafPk s.xa
              else hW pkSeed (adrsW 2 0 1 0) s.xa leafPk
  decide (root = pkRoot)


-- @@ L212-212 verbatim
end Demo

-- @@ L213-213 verbatim
end SLHDSA
