/-
  EvmAsm.Evm64.GasCost

  The two-dimensional Amsterdam gas charge used by the Evm64 model.
  Amsterdam split these charges into separate regular- and state-gas
  accumulators rather than renumbering one total.  The header check therefore
  takes a maximum over the two dimensions (`fork.py:370-375`), while the
  accumulators remain separate (`fork.py:1176-1182`).
  `regular` is the ordinary execution-gas component; `state` is the
  state-gas component (whose units are defined by the caller, for example
  bytes multiplied by the state-gas rate), not a second part of a total.
-/

module


-- @@ L16-16 verbatim
public section

-- @@ L17-17 verbatim
namespace EvmAsm.Evm64


-- @@ L19-24 verbatim
/-- A gas charge split into the independently accumulated regular- and
state-gas dimensions used by Amsterdam's header check. -/
structure GasCost where
  regular : Nat
  state : Nat
  deriving DecidableEq, Repr


-- @@ L26-26 verbatim
namespace GasCost


-- @@ L28-32 verbatim
/-- Add the two gas dimensions component-wise. -/
instance : Add GasCost where
  add a b :=
    { regular := a.regular + b.regular
      state := a.state + b.state }


-- @@ L34-36 verbatim
/-- The zero charge in both gas dimensions. -/
instance : Zero GasCost where
  zero := { regular := 0, state := 0 }


-- @@ L38-39 verbatim
@[simp] theorem add_regular (a b : GasCost) :
    (a + b).regular = a.regular + b.regular := rfl


-- @@ L41-42 verbatim
@[simp] theorem add_state (a b : GasCost) :
    (a + b).state = a.state + b.state := rfl


-- @@ L44-45 verbatim
@[simp] theorem zero_regular :
    (0 : GasCost).regular = 0 := rfl


-- @@ L47-48 verbatim
@[simp] theorem zero_state :
    (0 : GasCost).state = 0 := rfl


-- @@ L50-50 verbatim
end GasCost

-- @@ L51-51 verbatim
end EvmAsm.Evm64
