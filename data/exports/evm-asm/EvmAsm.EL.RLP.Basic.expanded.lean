/-
  EvmAsm.EL.RLP.Basic

  Core RLP (Recursive Length Prefix) types and encoding.
  Reference: Ethereum Yellow Paper, Appendix B.
-/

module


-- @@ L10-10 verbatim
@[expose] public section

-- @@ L11-11 verbatim
namespace EvmAsm.EL.RLP


-- @@ L13-13 verbatim
abbrev Byte := BitVec 8


-- @@ L15-19 verbatim
/-- An RLP item is either a byte string or a list of RLP items. -/
inductive RLPItem where
  | bytes : List Byte → RLPItem
  | list  : List RLPItem → RLPItem
  deriving Repr, BEq


-- @@ L21-31 verbatim
mutual
def RLPItem.decEq : (a b : RLPItem) → Decidable (a = b)
  | .bytes as, .bytes bs =>
    if h : as = bs then isTrue (by subst h; rfl)
    else isFalse (fun h' => h (RLPItem.bytes.inj h'))
  | .list as, .list bs =>
    match RLPItem.decEqList as bs with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (fun h' => h (RLPItem.list.inj h'))
  | .bytes _, .list _ => isFalse (fun h => by cases h)
  | .list _, .bytes _ => isFalse (fun h => by cases h)


-- @@ L33-41 verbatim
def RLPItem.decEqList : (a b : List RLPItem) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match RLPItem.decEq a b, RLPItem.decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (fun h' => h (List.cons.inj h' |>.1))
    | _, isFalse h => isFalse (fun h' => h (List.cons.inj h' |>.2))

-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
instance : DecidableEq RLPItem := RLPItem.decEq


-- @@ L46-46 verbatim
/-! ## Big-endian natural number encoding -/


-- @@ L48-53 verbatim
/-- Encode a natural number as minimal big-endian bytes. Zero maps to `[]`. -/
def Nat.toBytesBE : Nat → List Byte
  | 0 => []
  | n + 1 =>
    have : (n + 1) / 256 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by omega)
    Nat.toBytesBE ((n + 1) / 256) ++ [BitVec.ofNat 8 ((n + 1) % 256)]


-- @@ L55-58 verbatim
/-- Decode big-endian bytes to a natural number. -/
def Nat.fromBytesBE : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + Nat.fromBytesBE bs


-- @@ L60-60 verbatim
/-! ## RLP Encoding -/


-- @@ L62-74 verbatim
/-- Encode the prefix and data for a byte string. -/
def encodeBytes (data : List Byte) : List Byte :=
  match data with
  | [b] =>
    if b.toNat < 0x80 then [b]
    else [BitVec.ofNat 8 0x81, b]
  | _ =>
    let len := data.length
    if len ≤ 55 then
      [BitVec.ofNat 8 (0x80 + len)] ++ data
    else
      let lenBytes := Nat.toBytesBE len
      [BitVec.ofNat 8 (0xB7 + lenBytes.length)] ++ lenBytes ++ data


-- @@ L76-87 verbatim
/-- Generic short byte-string encoding, excluding the singleton special case. -/
theorem encodeBytes_short_of_length_ne_one (data : List Byte)
    (hLen : data.length ≤ 55) (hNeOne : data.length ≠ 1) :
    encodeBytes data = [BitVec.ofNat 8 (0x80 + data.length)] ++ data := by
  cases data with
  | nil => simp [encodeBytes]
  | cons a tail =>
      cases tail with
      | nil => exact False.elim (hNeOne rfl)
      | cons b tail =>
          have hLen' : tail.length + 1 + 1 ≤ 55 := by simpa using hLen
          simp [encodeBytes, hLen']


-- @@ L89-103 verbatim
/-- Encode an RLP item to bytes. -/
def encode : RLPItem → List Byte
  | .bytes data => encodeBytes data
  | .list items =>
    let payload := encodeItems items
    let len := payload.length
    if len ≤ 55 then
      [BitVec.ofNat 8 (0xC0 + len)] ++ payload
    else
      let lenBytes := Nat.toBytesBE len
      [BitVec.ofNat 8 (0xF7 + lenBytes.length)] ++ lenBytes ++ payload
where
  encodeItems : List RLPItem → List Byte
    | [] => []
    | item :: rest => encode item ++ encodeItems rest


-- @@ L105-105 verbatim
end EvmAsm.EL.RLP
