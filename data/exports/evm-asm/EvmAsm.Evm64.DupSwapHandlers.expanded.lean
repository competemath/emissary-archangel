/-
  EvmAsm.Evm64.DupSwapHandlers

  Generic pure handler-table entries for DUP1-16 and SWAP1-16 (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace DupSwapHandlers


-- @@ L16-16 verbatim
open EvmOpcode


-- @@ L18-23 verbatim
/-- Pure stack transform for DUPn. The index is the EVM opcode suffix, so
    `n = 1` duplicates the stack head. -/
def dupStack? (n : Nat) (stack : List EvmWord) : Option (List EvmWord) :=
  match stack[n - 1]? with
  | some word => some (word :: stack)
  | none => none


-- @@ L25-33 verbatim
/-- Replace the zero-based slot in a tail list, returning the replaced value
    and the updated tail. Used by SWAPn after peeling the stack head. -/
def replaceAt? : Nat → EvmWord → List EvmWord → Option (EvmWord × List EvmWord)
  | 0, new, old :: tail => some (old, new :: tail)
  | slot + 1, new, old :: tail =>
      match replaceAt? slot new tail with
      | some (target, tail') => some (target, old :: tail')
      | none => none
  | _, _, [] => none


-- @@ L35-43 verbatim
/-- Pure stack transform for SWAPn. The index is the EVM opcode suffix, so
    `n = 1` swaps the top two stack items. -/
def swapStack? (n : Nat) (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | top :: rest =>
      match replaceAt? (n - 1) top rest with
      | some (target, rest') => some (target :: rest')
      | none => none
  | [] => none


-- @@ L45-51 verbatim
/-- DUPn handler over the abstract interpreter state. Stack underflow marks the
    state invalid; gas/pc charging belongs to the later executable wrapper. -/
def dupHandler (n : Nat) : OpcodeHandler :=
  fun state =>
    match dupStack? n state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L53-59 verbatim
/-- SWAPn handler over the abstract interpreter state. Stack underflow marks the
    state invalid; gas/pc charging belongs to the later executable wrapper. -/
def swapHandler (n : Nat) : OpcodeHandler :=
  fun state =>
    match swapStack? n state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L61-75 verbatim
/-- Lookup surface for generic DUP/SWAP handlers. Invalid parameterized opcode
    values stay unimplemented rather than silently installing nonsensical
    handlers. -/
def dupSwapHandler? : EvmOpcode → Option OpcodeHandler
  | .DUP n =>
      if EvmOpcode.validDupIndex n then
        some (dupHandler n)
      else
        none
  | .SWAP n =>
      if EvmOpcode.validSwapIndex n then
        some (swapHandler n)
      else
        none
  | _ => none


-- @@ L77-80 verbatim
/-- Handler table containing the generic DUP1-16 and SWAP1-16 entries.
    Distinctive token: DupSwapHandlers.dupSwapHandlerTable #107. -/
def dupSwapHandlerTable : HandlerTable :=
  dupSwapHandler?


-- @@ L82-83 verbatim
@[simp] theorem dupStack?_one (word : EvmWord) (stack : List EvmWord) :
    dupStack? 1 (word :: stack) = some (word :: word :: stack) := rfl


-- @@ L85-87 verbatim
@[simp] theorem swapStack?_one
    (top next : EvmWord) (stack : List EvmWord) :
    swapStack? 1 (top :: next :: stack) = some (next :: top :: stack) := rfl


-- @@ L89-91 verbatim
@[simp] theorem replaceAt?_zero
    (new old : EvmWord) (tail : List EvmWord) :
    replaceAt? 0 new (old :: tail) = some (old, new :: tail) := rfl


-- @@ L93-106 verbatim
theorem dupStack?_eq_some_iff
    (n : Nat) (stack stack' : List EvmWord) :
    dupStack? n stack = some stack' ↔
      ∃ word, stack[n - 1]? = some word ∧ stack' = word :: stack := by
  constructor
  · intro h_stack
    cases h_word : stack[n - 1]? with
    | none =>
        simp [dupStack?, h_word] at h_stack
    | some word =>
        simp [dupStack?, h_word] at h_stack
        exact ⟨word, rfl, h_stack.symm⟩
  · rintro ⟨word, h_word, rfl⟩
    simp [dupStack?, h_word]


-- @@ L108-115 verbatim
theorem dupStack?_eq_none_iff
    (n : Nat) (stack : List EvmWord) :
    dupStack? n stack = none ↔ stack[n - 1]? = none := by
  cases h_word : stack[n - 1]? with
  | none =>
      simp [dupStack?, h_word]
  | some word =>
      simp [dupStack?, h_word]


-- @@ L117-138 verbatim
theorem swapStack?_eq_some_iff
    (n : Nat) (stack stack' : List EvmWord) :
    swapStack? n stack = some stack' ↔
      ∃ top rest target rest',
        stack = top :: rest ∧
        replaceAt? (n - 1) top rest = some (target, rest') ∧
        stack' = target :: rest' := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [swapStack?] at h_stack
    | cons top rest =>
        cases h_replace : replaceAt? (n - 1) top rest with
        | none =>
            simp [swapStack?, h_replace] at h_stack
        | some result =>
            obtain ⟨target, rest'⟩ := result
            simp [swapStack?, h_replace] at h_stack
            exact ⟨top, rest, target, rest', rfl, h_replace, h_stack.symm⟩
  · rintro ⟨top, rest, target, rest', rfl, h_replace, rfl⟩
    simp [swapStack?, h_replace]


-- @@ L140-160 verbatim
theorem swapStack?_eq_none_iff
    (n : Nat) (stack : List EvmWord) :
    swapStack? n stack = none ↔
      stack = [] ∨
        ∃ top rest, stack = top :: rest ∧
          replaceAt? (n - 1) top rest = none := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        exact Or.inl rfl
    | cons top rest =>
        right
        cases h_replace : replaceAt? (n - 1) top rest with
        | none =>
            exact ⟨top, rest, rfl, h_replace⟩
        | some result =>
            simp [swapStack?, h_replace] at h_stack
  · rintro (rfl | ⟨top, rest, rfl, h_replace⟩)
    · simp [swapStack?]
    · simp [swapStack?, h_replace]


-- @@ L162-163 verbatim
@[simp] theorem dupSwapHandlerTable_eq :
    dupSwapHandlerTable = dupSwapHandler? := rfl


-- @@ L165-168 verbatim
theorem dupSwapHandler?_DUP_of_valid {n : Nat}
    (h_valid : EvmOpcode.validDupIndex n = true) :
    dupSwapHandler? (.DUP n) = some (dupHandler n) := by
  simp [dupSwapHandler?, h_valid]


-- @@ L170-173 verbatim
theorem dupSwapHandler?_DUP_of_invalid {n : Nat}
    (h_valid : EvmOpcode.validDupIndex n = false) :
    dupSwapHandler? (.DUP n) = none := by
  simp [dupSwapHandler?, h_valid]


-- @@ L175-178 verbatim
theorem dupSwapHandler?_SWAP_of_valid {n : Nat}
    (h_valid : EvmOpcode.validSwapIndex n = true) :
    dupSwapHandler? (.SWAP n) = some (swapHandler n) := by
  simp [dupSwapHandler?, h_valid]


-- @@ L180-183 verbatim
theorem dupSwapHandler?_SWAP_of_invalid {n : Nat}
    (h_valid : EvmOpcode.validSwapIndex n = false) :
    dupSwapHandler? (.SWAP n) = none := by
  simp [dupSwapHandler?, h_valid]


-- @@ L185-187 verbatim
@[simp] theorem eq_dupHandler_iff (n : Nat) (handler : OpcodeHandler) :
    dupHandler n = handler ↔ handler = dupHandler n := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L189-191 verbatim
@[simp] theorem eq_swapHandler_iff (n : Nat) (handler : OpcodeHandler) :
    swapHandler n = handler ↔ handler = swapHandler n := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L193-200 verbatim
theorem dupSwapHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    dupSwapHandler? opcode = some handler ↔
      (∃ n, opcode = .DUP n ∧ EvmOpcode.validDupIndex n = true ∧
        handler = dupHandler n) ∨
        (∃ n, opcode = .SWAP n ∧ EvmOpcode.validSwapIndex n = true ∧
          handler = swapHandler n) := by
  cases opcode <;> simp [dupSwapHandler?]


-- @@ L202-207 verbatim
theorem dupSwapHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    dupSwapHandler? opcode = none ↔
      (∀ n, opcode = .DUP n → EvmOpcode.validDupIndex n = false) ∧
        (∀ n, opcode = .SWAP n → EvmOpcode.validSwapIndex n = false) := by
  cases opcode <;> simp [dupSwapHandler?]


-- @@ L209-213 verbatim
theorem dupHandler_stack_of_dupStack?_some
    {n : Nat} {state : EvmState} {stack' : List EvmWord}
    (h_stack : dupStack? n state.stack = some stack') :
    (dupHandler n state).stack = stack' := by
  simp [dupHandler, h_stack]


-- @@ L215-219 verbatim
theorem swapHandler_stack_of_swapStack?_some
    {n : Nat} {state : EvmState} {stack' : List EvmWord}
    (h_stack : swapStack? n state.stack = some stack') :
    (swapHandler n state).stack = stack' := by
  simp [swapHandler, h_stack]


-- @@ L221-225 verbatim
theorem dupHandler_status_of_dupStack?_none
    {n : Nat} {state : EvmState}
    (h_stack : dupStack? n state.stack = none) :
    (dupHandler n state).status = .error := by
  simp [dupHandler, h_stack]


-- @@ L227-231 verbatim
theorem swapHandler_status_of_swapStack?_none
    {n : Nat} {state : EvmState}
    (h_stack : swapStack? n state.stack = none) :
    (swapHandler n state).status = .error := by
  simp [swapHandler, h_stack]


-- @@ L233-239 verbatim
theorem dispatchOpcode_dupSwapHandlerTable_DUP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode dupSwapHandlerTable (.DUP n) state =
      dupHandler n state := by
  exact HandlerTable.dispatchOpcode_some
    (dupSwapHandler?_DUP_of_valid h_valid) state


-- @@ L241-247 verbatim
theorem dispatchOpcode_dupSwapHandlerTable_SWAP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode dupSwapHandlerTable (.SWAP n) state =
      swapHandler n state := by
  exact HandlerTable.dispatchOpcode_some
    (dupSwapHandler?_SWAP_of_valid h_valid) state


-- @@ L249-256 verbatim
theorem dispatchOpcode_dupSwapHandlerTable_DUP_of_valid_status_of_some
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : dupStack? n state.stack = some stack') :
    (HandlerTable.dispatchOpcode dupSwapHandlerTable (.DUP n) state).status =
      state.status := by
  rw [dispatchOpcode_dupSwapHandlerTable_DUP_of_valid h_valid state]
  simp [dupHandler, h_stack, EvmState.withStack]


-- @@ L258-265 verbatim
theorem dispatchOpcode_dupSwapHandlerTable_SWAP_of_valid_status_of_some
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : swapStack? n state.stack = some stack') :
    (HandlerTable.dispatchOpcode dupSwapHandlerTable (.SWAP n) state).status =
      state.status := by
  rw [dispatchOpcode_dupSwapHandlerTable_SWAP_of_valid h_valid state]
  simp [swapHandler, h_stack, EvmState.withStack]


-- @@ L267-273 verbatim
theorem dispatchOpcode?_dupSwapHandlerTable_DUP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validDupIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? dupSwapHandlerTable (.DUP n) state =
      some (dupHandler n state) := by
  exact HandlerTable.dispatchOpcode?_some
    (dupSwapHandler?_DUP_of_valid h_valid) state


-- @@ L275-281 verbatim
theorem dispatchOpcode?_dupSwapHandlerTable_SWAP_of_valid
    {n : Nat} (h_valid : EvmOpcode.validSwapIndex n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? dupSwapHandlerTable (.SWAP n) state =
      some (swapHandler n state) := by
  exact HandlerTable.dispatchOpcode?_some
    (dupSwapHandler?_SWAP_of_valid h_valid) state


-- @@ L283-283 verbatim
end DupSwapHandlers

-- @@ L284-284 verbatim
end EvmAsm.Evm64
