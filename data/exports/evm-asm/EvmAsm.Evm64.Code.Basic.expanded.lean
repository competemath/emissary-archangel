/-
  EvmAsm.Evm64.Code.Basic

  Pure byte helpers for CODECOPY executable-spec bridges
  (GH #107 / GH #118).
-/

module


-- @@ L10-10 verbatim
@[expose] public section

-- @@ L11-11 verbatim
namespace EvmAsm.Evm64

-- @@ L12-12 verbatim
namespace Code


-- @@ L14-17 verbatim
/-- Byte offset of the M33 `codeSize` cell within the dispatcher env block.
    Both dispatcher prologues seed this with the exact running-bytecode length;
    CODESIZE, CODECOPY, and JUMP/JUMPI bounds checks read it. -/
def codeSizeOff : Nat := 496


-- @@ L19-21 verbatim
/-- Read one byte from executable code, returning zero past the end. -/
def byte (code : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < code.length then code[idx] else 0


-- @@ L23-28 verbatim
/-- Bytes written by CODECOPY:
    `size` bytes from `code` starting at `codeOffset`, with out-of-bounds
    reads producing zero. Distinctive token: Code.copyBytes #107 #118. -/
def copyBytes
    (code : List (BitVec 8)) (codeOffset size : Nat) : List (BitVec 8) :=
  (List.range size).map (fun i => byte code (codeOffset + i))


-- @@ L30-33 verbatim
theorem byte_of_lt {code : List (BitVec 8)} {idx : Nat}
    (h : idx < code.length) :
    byte code idx = code[idx] := by
  simp [byte, h]


-- @@ L35-38 verbatim
theorem byte_of_ge {code : List (BitVec 8)} {idx : Nat}
    (h : code.length ≤ idx) :
    byte code idx = 0 := by
  simp [byte, show ¬idx < code.length from by omega]


-- @@ L40-42 verbatim
@[simp] theorem byte_nil (idx : Nat) :
    byte [] idx = 0 := by
  exact byte_of_ge (code := []) (idx := idx) (by simp)


-- @@ L44-47 verbatim
@[simp] theorem copyBytes_length
    (code : List (BitVec 8)) (codeOffset size : Nat) :
    (copyBytes code codeOffset size).length = size := by
  simp [copyBytes]


-- @@ L49-52 verbatim
@[simp] theorem copyBytes_zero
    (code : List (BitVec 8)) (codeOffset : Nat) :
    copyBytes code codeOffset 0 = [] := by
  simp [copyBytes]


-- @@ L54-60 verbatim
theorem copyBytes_get
    {code : List (BitVec 8)} {codeOffset size i : Nat}
    (h : i < size) :
    (copyBytes code codeOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = byte code (codeOffset + i) := by
  simp [copyBytes]


-- @@ L62-69 verbatim
theorem copyBytes_get_of_in_bounds
    {code : List (BitVec 8)} {codeOffset size i : Nat}
    (h : i < size)
    (hsrc : codeOffset + i < code.length) :
    (copyBytes code codeOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = code[codeOffset + i] := by
  rw [copyBytes_get h, byte_of_lt hsrc]


-- @@ L71-78 verbatim
theorem copyBytes_get_of_out_of_bounds
    {code : List (BitVec 8)} {codeOffset size i : Nat}
    (h : i < size)
    (hsrc : code.length ≤ codeOffset + i) :
    (copyBytes code codeOffset size)[i]'(by
      simpa [copyBytes_length] using h)
      = 0 := by
  rw [copyBytes_get h, byte_of_ge hsrc]


-- @@ L80-82 verbatim
@[simp] theorem copyBytes_nil (codeOffset size : Nat) :
    copyBytes [] codeOffset size = List.replicate size 0 := by
  simp [copyBytes, List.map_const']


-- @@ L84-84 verbatim
end Code

-- @@ L85-85 verbatim
end EvmAsm.Evm64
